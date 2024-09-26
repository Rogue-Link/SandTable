--------------------------------- MODULE etcdraft ---------------------------------
\* Copyright 2024 The etcd Authors
\*
\* Licensed under the Apache License, Version 2.0 (the "License");
\* you may not use this file except in compliance with the License.
\* You may obtain a copy of the License at
\*
\*     http://www.apache.org/licenses/LICENSE-2.0
\*
\* Unless required by applicable law or agreed to in writing, software
\* distributed under the License is distributed on an "AS IS" BASIS,
\* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
\* See the License for the specific language governing permissions and
\* limitations under the License.
\*
\*
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro, 2015 Brandon Amos and Huanchen Zhang,
\* 2016 Daniel Ricketts, 2021 George Pîrlea and Darius Foo.
\*
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, Integers, Bags, FiniteSets, Sequences, SequencesExt, FiniteSetsExt, BagsExt, TLC

\* The initial and global set of server IDs.
CONSTANTS InitServer, Server

\* Log metadata to distinguish values from configuration changes.
CONSTANT ValueEntry, ConfigEntry

\* Server states.
CONSTANTS 
    \* @type: Str;
    Follower,
    \* @type: Str;
    Candidate,
    \* @type: Str;
    Leader

\* A reserved value.
CONSTANTS 
    \* @type: Int;
    Nil, Parameters

\* Message types:
CONSTANTS 
    \* @type: Str;
    RequestVoteRequest,
    \* @type: Str;
    RequestVoteResponse,
    \* @type: Str;
    AppendEntriesRequest,
    \* @type: Str;
    AppendEntriesResponse


----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. We differentiate between the message types to support Apalache.
VARIABLE
    \* @typeAlias: ENTRY = [term: Int, value: Int];
    \* @typeAlias: LOGT = Seq(ENTRY);
    \* @typeAlias: RVREQT = [mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, src: Int, dst: Int];
    \* @typeAlias: RVRESPT = [mtype: Str, mterm: Int, mvoteGranted: Bool, src: Int, dst: Int ];
    \* @typeAlias: AEREQT = [mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: LOGT, mcommitIndex: Int, src: Int, dst: Int ];
    \* @typeAlias: AERESPT = [mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, src: Int, dst: Int ];
    \* @typeAlias: MSG = [ wrapped: Bool, mtype: Str, mterm: Int, src: Int, dst: Int, RVReq: RVREQT, RVResp: RVRESPT, AEReq: AEREQT, AEResp: AERESPT ];
    \* @type: MSG -> Int;
    msgs
VARIABLE 
    pendingMessages
messageVars == <<msgs, pendingMessages>>

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE 
    \* @type: Int -> Int;
    currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE 
    \* @type: Int -> Str;
    state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE 
    \* @type: Int -> Int;
    votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE 
    \* @type: Int -> [ entries: LOGT, len: Int ];
    log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE 
    \* @type: Int -> Int;
    commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesGranted
\* @type: Seq(Int -> Set(Int));
candidateVars == <<votesResponded, votesGranted>>

\* The following variables are used only on leaders:
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE 
    \* @type: Int -> (Int -> Int);
    matchIndex
VARIABLE
    pendingConfChangeIndex
leaderVars == <<matchIndex, pendingConfChangeIndex>>

\* @type: Int -> [jointConfig: Seq(Set(int)), learners: Set(int)]
VARIABLE 
    config
VARIABLE 
    reconfigCount

configVars == <<config, reconfigCount>>

VARIABLE 
    durableState

(***************************************************************************
  Network variables and instance
 ***************************************************************************)
VARIABLES netman, netcmd
INSTANCE FifoNetwork WITH FLUSH_DISCONN <- TRUE, NULL_MSG <- Nil,
    _msgs <- msgs, _netman <- netman, _netcmd <- netcmd
VARIABLE inv
\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messageVars, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, inv, netcmd, netman>>


----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(c) == {i \in SUBSET(c) : Cardinality(i) * 2 > Cardinality(c)}

\* The term of the last entry in a log, or 0 if the log is empty.
\* @type: LOGT => Int;
LastTerm(xlog) == IF xlog = <<>> THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of msgs, return a
\* new bag of msgs with one more m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithMessage(m, messages) == messages (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of msgs, return
\* a new bag of msgs with one less m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithoutMessage(m, messages) == messages (-) SetToBag({m})

\* Add a message to the bag of pendingMessages.
SendDirect(m) == 
    pendingMessages' = WithMessage(m, pendingMessages)

\* All pending msgs sent from node i
PendingMessages(i) == 
    FoldBag(LAMBDA x, y: IF y.src = i THEN BagAdd(x,y) ELSE x, EmptyBag, pendingMessages)

\* Remove all msgs in pendingMessages that were sent from node i
ClearPendingMessages(i) ==
    pendingMessages (-) PendingMessages(i)

RECURSIVE AppendTimes(_, _, _)

AppendTimes(x, y, k) ==
    IF k = 0 THEN x
    ELSE AppendTimes(Append(x, y), y, k - 1)

ExpandMessages(mssgs) == 
    FoldBag(LAMBDA x, y: IF mssgs[y] /= 0 THEN Append(x, y) ELSE x, <<>>, mssgs)

\* Move all msgs which was sent from node i in pendingMessages to msgs
SendPendingMessages(i) ==
    LET messages == PendingMessages(i)
    IN /\ NetUpdate2(NetBatchAddMsg(ExpandMessages(messages)), <<"SendPendingMessages", i>>)
       /\ pendingMessages' = pendingMessages (-) messages

\* Remove a message from the bag of msgs. Used when a server is done
DiscardDirect(m) ==
    msgs' = WithoutMessage(m, msgs)

\* Combination of Send and Discard
ReplyDirect(response, request) ==
    /\ pendingMessages' = WithMessage(response, pendingMessages)
    /\ msgs' = WithoutMessage(request, msgs)

\* Default: change when needed
 Send(m) == SendDirect(m)
 Reply(response, request) == ReplyDirect(response, request) 
 Discard(m) == DiscardDirect(m)
     
MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)

GetJointConfig(i) == 
    config[i].jointConfig

GetConfig(i) == 
    GetJointConfig(i)[1]

GetOutgoingConfig(i) ==
    GetJointConfig(i)[2]

IsJointConfig(i) ==
    /\ GetJointConfig(i)[2] # {}

GetLearners(i) ==
    config[i].learners

\* Apply conf change log entry to configuration
ApplyConfigUpdate(i, k) ==
    [config EXCEPT ![i]= [jointConfig |-> << log[i][k].value.newconf, {} >>, learners |-> log[i][k].value.learners]]

CommitTo(i, c) ==
    commitIndex' = [commitIndex EXCEPT ![i] = Max({@, c})]

CurrentLeaders == {i \in Server : state[i] = Leader}

PersistState(i) == 
    durableState' = [durableState EXCEPT ![i] = [
        currentTerm |-> currentTerm[i],
        votedFor |-> votedFor[i],
        log |-> Len(log[i]),
        commitIndex |-> commitIndex[i],
        config |-> config[i]
    ]]

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i], i)
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]
----
GetParameterSet(p)  == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE {}
\* Define initial values for all variables
InitMessageVars == /\ pendingMessages = EmptyBag
InitServerVars == /\ currentTerm = [i \in Server |-> 0]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  /\ pendingConfChangeIndex = [i \in Server |-> 0]
InitLogVars == /\ log          = [i \in Server |-> <<>>]
               /\ commitIndex  = [i \in Server |-> 0]
InitConfigVars == /\ config = [i \in Server |-> [ jointConfig |-> <<InitServer, {}>>, learners |-> {}]]
                  /\ reconfigCount = 0 
InitDurableState == 
    durableState = [ i \in Server |-> [
        currentTerm |-> currentTerm[i],
        votedFor |-> votedFor[i],
        log |-> Len(log[i]),
        commitIndex |-> commitIndex[i],
        config |-> config[i]
    ]]
InitInv == inv = <<>>

Init == /\ InitMessageVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitConfigVars
        /\ InitDurableState
        /\ InitInv
        /\ InitFifoNetworkAddNetman(InitServer, <<"init", Cardinality(InitServer)>>, 
            [ n_op |-> 0, n_ae |-> 0, n_elec |-> 0, n_sent |-> 0, n_wire |-> 0, n_cure |-> 0, n_part |-> 0, no_inv |-> GetParameterSet("NoInv")])

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, commitIndex, votedFor, log, and config in durable state.
\* @type: Int => Bool;
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
    /\ pendingMessages' = ClearPendingMessages(i)
    /\ currentTerm' = [currentTerm EXCEPT ![i] = durableState[i].currentTerm]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = durableState[i].commitIndex]
    /\ votedFor' = [votedFor EXCEPT ![i] = durableState[i].votedFor]
    /\ log' = [log EXCEPT ![i] = SubSeq(@, 1, durableState[i].log)]
    /\ config' = [config EXCEPT ![i] = durableState[i].config]
    /\ NetUpdate2(NetmanIncField("n_cure", NetNoAction("Restart")), <<"Restart", i>>)
    /\ UNCHANGED <<msgs, durableState, reconfigCount>>

\* Server i times out and starts a new election.
\* @type: Int => Bool;
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ i \in GetConfig(i)
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ votedFor' = [votedFor EXCEPT ![i] = i]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ NetUpdate2(NetmanIncField("n_elec", NetNoAction("Timeout")), <<"Timeout", i>>)
              /\ UNCHANGED <<messageVars, leaderVars, logVars, configVars, durableState>>

\* Candidate i sends j a RequestVote request.
\* @type: (Int, Int) => Bool;
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \in ((GetConfig(i) \union GetLearners(i)) \ votesResponded[i])
    /\ IF i # j 
        THEN LET m1 == ([mtype            |-> RequestVoteRequest,
                        mterm            |-> currentTerm[i],
                        mlastLogTerm     |-> LastTerm(log[i]),
                        mlastLogIndex    |-> Len(log[i]),
                        src          |-> i,
                        dst            |-> j])
             IN /\ Send(m1)
                /\ NetUpdate2(NetmanIncField("n_sent", NetNoAction("RequestVote")), <<"RequestVote", i, j>>)
        ELSE LET m2 == ([mtype            |-> RequestVoteResponse,
                        mterm            |-> currentTerm[i],
                        mvoteGranted     |-> TRUE,
                        src          |-> i,
                        dst            |-> i])
             IN /\ Send(m2)
                /\ NetUpdate2(NetmanIncField("n_sent", NetNoAction("RequestVote")), <<"RequestVote", i, j>>)
    /\ UNCHANGED <<msgs, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>>

\* Leader i sends j an AppendEntries request containing entries in [b,e) range.
\* N.B. range is right open
\* @type: (Int, Int, <<Int, Int>>, Int) => Bool;
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    /\ LET 
        prevLogIndex == range[1] - 1
        \* The following upper bound on prevLogIndex is unnecessary
        \* but makes verification substantially simpler.
        prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN
                            log[i][prevLogIndex].term
                        ELSE
                            0
        \* Send the entries
        lastEntry == Min({Len(log[i]), range[2]-1})
        entries == SubSeq(log[i], range[1], lastEntry)
        commit == IF subtype = "heartbeat" THEN Min({commitIndex[i], matchIndex[i][j]}) ELSE Min({commitIndex[i], lastEntry})
       IN /\ LET m1 == ( [mtype          |-> AppendEntriesRequest,
                        msubtype       |-> subtype,
                        mterm          |-> currentTerm[i],
                        mprevLogIndex  |-> prevLogIndex,
                        mprevLogTerm   |-> prevLogTerm,
                        mentries       |-> entries,
                        mcommitIndex   |-> commit,
                        src        |-> i,
                        dst          |-> j])
             IN /\ Send(m1)
                /\ NetUpdate2(NetmanIncField("n_ae", NetNoAction("AppendEntriesInRangeToPeer")), <<"AppendEntriesInRangeToPeer", subtype, i, j, range>>)
          /\ UNCHANGED <<msgs, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>> 

\* etcd leader sends MsgAppResp to itself immediately after appending log entry 
AppendEntriesToSelf(i) ==
    /\ state[i] = Leader
    /\ LET m1 == ([mtype           |-> AppendEntriesResponse,
                  msubtype        |-> "app",
                  mterm           |-> currentTerm[i],
                  msuccess        |-> TRUE,
                  mmatchIndex     |-> Len(log[i]),
                  src         |-> i,
                  dst           |-> i])
       IN /\ Send(m1)
          /\ NetUpdate2(NetmanIncField("n_sent", NetNoAction("AppendEntriesToSelf")), <<"AppendEntriesToSelf", i>>)
    /\ UNCHANGED <<msgs, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>>

AppendEntries(i, j, range) ==
    AppendEntriesInRangeToPeer("app", i, j, range)

Heartbeat(i, j) ==
    \* heartbeat is equivalent to an append-entry request with 0 entry index 1
    AppendEntriesInRangeToPeer("heartbeat", i, j, <<1,1>>)

SendSnapshot(i, j, index) ==
    AppendEntriesInRangeToPeer("snapshot", i, j, <<1,index+1>>)
 
\* Candidate i transitions to leader.
\* @type: Int => Bool;
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum(GetConfig(i))
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> IF j = i THEN Len(log[i]) ELSE 0]]
    /\ NetUpdate2(NetNoAction("BecomeLeader"), <<"BecomeLeader", i>>)
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, pendingConfChangeIndex, candidateVars, logVars, configVars, durableState>>
    
Replicate(i, v, t) == 
    /\ t \in {ValueEntry, ConfigEntry}
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     type  |-> t,
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]

\* Leader i receives a client request to add v to the log.
\* @type: (Int, Int) => Bool;
ClientRequest(i, v) ==
    /\ Replicate(i, [val |-> v], ValueEntry)
    /\ NetUpdate2(NetmanIncField("n_op", NetNoAction("ClientRequest")), <<"ClientRequest", i, v>>)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, commitIndex, configVars, durableState>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* @type: Int => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {k \in GetConfig(i) : matchIndex[i][k] >= index}
           logSize == Len(log[i])
           \* logSize == MaxLogLength
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..logSize :
                                Agree(index) \in Quorum(GetConfig(i))}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN
        /\ CommitTo(i, newCommitIndex)
        /\ NetUpdate2(NetNoAction("AdvanceCommitIndex"), <<"AdvanceCommitIndex", i>>)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, log, configVars, durableState>>

    
\* Leader i adds a new server j or promote learner j
AddNewServer(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i) \union {j}, learners |-> GetLearners(i)], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
       ELSE 
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState>>

\* Leader i adds a leaner j to the cluster.
AddLearner(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i) \union GetLearners(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN 
            /\ Replicate(i, [newconf |-> GetConfig(i), learners |-> GetLearners(i) \union {j}], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
       ELSE 
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState>>

\* Leader i removes a server j (possibly itself) from the cluster.
DeleteServer(i, j) ==
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i) \ {j}, learners |-> GetLearners(i) \ {j}], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
       ELSE 
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState>>

ApplySimpleConfChange(i) ==
    /\ ~IsJointConfig(i)
    /\ LET k == SelectLastInSubSeq(log[i], 1, commitIndex[i], LAMBDA x: x.type = ConfigEntry)
       IN 
            /\ k > 0
            /\ k <= commitIndex[i]
            /\ config' = ApplyConfigUpdate(i, k)
            /\ IF state[i] = Leader /\ pendingConfChangeIndex[i] >= k THEN 
                /\ reconfigCount' = reconfigCount + 1
                /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
               ELSE UNCHANGED <<reconfigCount, pendingConfChangeIndex>>
            /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, logVars, durableState>>
    
Ready(i) == 
    /\ PersistState(i)
    /\ SendPendingMessages(i)
    /\ UNCHANGED <<serverVars, leaderVars, candidateVars, logVars, configVars, logVars>>

BecomeFollowerOfTerm(i, t) ==
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = t]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ NetUpdate2(NetNoAction("BecomeFollowerOfTerm"), <<"BecomeFollowerOfTerm", i, t>>)
    /\ IF currentTerm[i] # t THEN  
            votedFor' = [votedFor    EXCEPT ![i] = Nil]
       ELSE 
            UNCHANGED <<votedFor>>

StepDownToFollower(i) ==
    /\ state[i] \in {Leader, Candidate}
    /\ BecomeFollowerOfTerm(i, currentTerm[i])
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, configVars, durableState>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: (Int, Int, RVREQT) => Bool;
HandleRequestVoteRequest(i, j, m) == 
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ LET m1 == ([mtype        |-> RequestVoteResponse,
                     mterm        |-> currentTerm[i],
                     mvoteGranted |-> grant,
                     src      |-> i,
                     dst        |-> j])
          IN /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "HandleMsgRVR", i, j>>)
             /\ Send(m1)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, configVars, durableState>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, RVRESPT) => Bool;
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ NetUpdate2(NetDelMsg(m), <<"HandleRequestVoteResponse", i, j>>)
    /\ UNCHANGED <<pendingMessages, serverVars, votedFor, leaderVars, logVars, configVars, durableState>>

\* @type: (Int, Int, AEREQT, Bool) => Bool;
RejectAppendEntriesRequest(i, j, m, logOk) ==
    /\ \/ m.mterm < currentTerm[i]
       \/ /\ m.mterm = currentTerm[i]
          /\ state[i] = Follower
          /\ \lnot logOk
    /\ LET m1 == ([mtype           |-> AppendEntriesResponse,
                   msubtype        |-> "app",
                   mterm           |-> currentTerm[i],
                   msuccess        |-> FALSE,
                   mmatchIndex     |-> 0,
                   src         |-> i,
                   dst           |-> j])
       IN /\ NetUpdate2(NetDelMsg(m), <<"RejectAppendEntriesRequest", "RejectAppendEntriesRequest", i, j>>)
          /\ Send(m1)
    /\ UNCHANGED <<serverVars, logVars, configVars, durableState>>

\* @type: (Int, MSG) => Bool;
ReturnToFollowerState(i, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, logVars, configVars, durableState>> 

HasNoConflict(i, index, ents) ==
    /\ index <= Len(log[i]) + 1
    /\ \A k \in 1..Len(ents): index + k - 1 <= Len(log[i]) => log[i][index+k-1].term = ents[k].term

\* @type: (Int, Int, Int, AEREQT) => Bool;
AppendEntriesAlreadyDone(i, j, index, m) ==
    /\ \/ index <= commitIndex[i]
       \/ /\ index > commitIndex[i]
          /\ \/ m.mentries = << >>
             \/ /\ m.mentries /= << >>
                /\ m.mprevLogIndex + Len(m.mentries) <= Len(log[i])
                /\ HasNoConflict(i, index, m.mentries)          
    /\ IF index <= commitIndex[i] THEN 
            IF m.msubtype = "heartbeat" THEN CommitTo(i, m.mcommitIndex) ELSE UNCHANGED commitIndex
       ELSE 
            CommitTo(i, Min({m.mcommitIndex, m.mprevLogIndex+Len(m.mentries)}))
    /\ LET m1 == ([  mtype           |-> AppendEntriesResponse,
                     msubtype        |-> m.msubtype,
                     mterm           |-> currentTerm[i],
                     msuccess        |-> TRUE,
                     mmatchIndex     |-> IF m.msubtype = "heartbeat" \/ index > commitIndex[i] THEN m.mprevLogIndex+Len(m.mentries) ELSE commitIndex[i],
                     src         |-> i,
                     dst           |-> j])
       IN /\ NetUpdate2(NetDelMsg(m), <<"AppendEntriesAlreadyDone", "AppendEntriesAlreadyDone", i, j>>)
          /\ Send(m1)
    /\ UNCHANGED <<serverVars, log, configVars, durableState>>

\* @type: (Int, Int, AEREQT) => Bool;
ConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ ~HasNoConflict(i, index, m.mentries)
    /\ log' = [log EXCEPT ![i] = SubSeq(@, 1, Len(@) - 1)]
    /\ NetUpdate2(NetNoAction("ConflictAppendEntriesRequest"), <<"ConflictAppendEntriesRequest", i, index>>)
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState>>

\* @type: (Int, AEREQT) => Bool;
NoConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ HasNoConflict(i, index, m.mentries)
    /\ log' = [log EXCEPT ![i] = @ \o SubSeq(m.mentries, Len(@)-index+2, Len(m.mentries))]
    /\ NetUpdate2(NetNoAction("NoConflictAppendEntriesRequest"), <<"NoConflictAppendEntriesRequest", i, index>>)
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState>>

\* @type: (Int, Int, Bool, AEREQT) => Bool;
AcceptAppendEntriesRequest(i, j, logOk, m) ==
    \* accept request
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Follower
    /\ logOk
    /\ LET index == m.mprevLogIndex + 1
       IN \/ AppendEntriesAlreadyDone(i, j, index, m)
          \/ ConflictAppendEntriesRequest(i, index, m)
          \/ NoConflictAppendEntriesRequest(i, index, m)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* @type: (Int, Int, AEREQT) => Bool;
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN 
       /\ m.mterm <= currentTerm[i]
       /\ \/ RejectAppendEntriesRequest(i, j, m, logOk)
          \/ ReturnToFollowerState(i, m)
          \/ AcceptAppendEntriesRequest(i, j, logOk, m)
       /\ UNCHANGED <<candidateVars, leaderVars, configVars, durableState>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, AERESPT) => Bool;
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex})]
          /\ UNCHANGED <<pendingConfChangeIndex>>
       \/ /\ \lnot m.msuccess \* not successful
          /\ UNCHANGED <<leaderVars>>
    /\ NetUpdate2(NetDelMsg(m), <<"HandleAppendEntriesResponse", i, j>>)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, logVars, configVars, durableState>>

\* Any RPC with a newer term causes the recipient to advance its term first.
\* @type: (Int, Int, MSG) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ BecomeFollowerOfTerm(i, m.mterm)
       \* msgs is unchanged so m can be processed further.
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, configVars, durableState>>

\* Responses with stale terms are ignored.
\* @type: (Int, Int, MSG) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ NetUpdate2(NetDelMsg(m), <<"DropStaleResponse", i, j>>)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>>

\* Receive a message.
ReceiveDirect(m) ==
    LET i == m.dst
        j == m.src
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
    \/ UpdateTerm(i, j, m)
    \/  /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m)
    \/  /\ m.mtype = RequestVoteResponse
        /\  \/ DropStaleResponse(i, j, m)
            \/ HandleRequestVoteResponse(i, j, m)
    \/  /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)
    \/  /\ m.mtype = AppendEntriesResponse
        /\ \/ DropStaleResponse(i, j, m)
           \/ HandleAppendEntriesResponse(i, j, m)

Receive(m) == ReceiveDirect(m)

NextRequestVoteRequest == \E m \in DOMAIN msgs : m.mtype = RequestVoteRequest /\ Receive(m)
NextRequestVoteResponse == \E m \in DOMAIN msgs : m.mtype = RequestVoteResponse /\ Receive(m)
NextAppendEntriesRequest == \E m \in DOMAIN msgs : m.mtype = AppendEntriesRequest /\ Receive(m)
NextAppendEntriesResponse == \E m \in DOMAIN msgs : m.mtype = AppendEntriesResponse /\ Receive(m)

\* End of message handlers.


(***************************************************************************)
(* The main safety properties are below                                    *)
(***************************************************************************)
----

ASSUME DistinctRoles == /\ Leader /= Candidate
                        /\ Candidate /= Follower
                        /\ Follower /= Leader

ASSUME DistinctMessageTypes == /\ RequestVoteRequest /= AppendEntriesRequest
                               /\ RequestVoteRequest /= RequestVoteResponse
                               /\ RequestVoteRequest /= AppendEntriesResponse
                               /\ AppendEntriesRequest /= RequestVoteResponse
                               /\ AppendEntriesRequest /= AppendEntriesResponse
                               /\ RequestVoteResponse /= AppendEntriesResponse

----
\* Correctness invariants

\* The prefix of the log of server i that has been committed
Committed(i) == SubSeq(log[i],1,commitIndex[i])

\* The current term of any server is at least the term
\* of any message sent by that server
\* @type: MSG => Bool;
MessageTermsLtCurrentTerm(m) ==
    m.mterm <= currentTerm[m.src]

\* Committed log entries should never conflict between servers
LogInv ==
    \A i, j \in Server :
        \/ IsPrefix(Committed(i),Committed(j)) 
        \/ IsPrefix(Committed(j),Committed(i))


\* There should not be more than one leader per term at the same time
\* Note that this does not rule out multiple leaders in the same term at different times
MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* A leader always has the greatest index for its current term
ElectionSafetyInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            MaxOrZero({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            MaxOrZero({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})

\* Every (index, term) pair determines a log prefix
LogMatchingInv ==
    \A i, j \in Server :
        \A n \in (1..Len(log[i])) \cap (1..Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* When two candidates competes in a campaign, if a follower voted to
\* a candidate that did not win in the end, the follower's votedFor will 
\* not reset nor change to the winner (the other candidate) because its 
\* term remains same. This will violate this invariant.
\*
\* This invariant can be false because a server's votedFor is not reset
\* for msgs with same term. Refer to the case below.
\* 1. This is a 3 node cluster with nodes A, B, and C. Let's assume they are all followers with same term 1 and log at beginning.
\* 2. Now B and C starts compaign and both become candidates of term 2.
\* 3. B requests vote to A and A grant it. Now A is a term 2 follower whose votedFor is B.
\* 4. A's response to B is lost.
\* 5. C requests vote to B and B grant it. Now B is a term 2 follower whose votedFor is C. 
\* 6. C becomes leader of term 2.
\* 7. C replicates logs to A but not B. 
\* 8. A's votedFor is not changed because the incoming msgs has same term (see UpdateTerm and ReturnToFollowerState)
\* 9. Now the commited log in A will exceed B's log. The invariant is violated.
\* VotesGrantedInv ==
\*     \A i, j \in Server :
\*         \* if i has voted for j
\*         votedFor[i] = j =>
\*             IsPrefix(Committed(i), log[j])

\* All committed entries are contained in the log
\* of at least one server in every quorum
QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
        \E j \in S :
            IsPrefix(Committed(i), log[j])

\* The "up-to-date" check performed by servers
\* before issuing a vote implies that i receives
\* a vote from j only if i has all of j's committed
\* entries
MoreUpToDateCorrectInv ==
    \A i, j \in Server :
       (\/ LastTerm(log[i]) > LastTerm(log[j])
        \/ /\ LastTerm(log[i]) = LastTerm(log[j])
           /\ Len(log[i]) >= Len(log[j])) =>
       IsPrefix(Committed(j), log[i])

\* If a log entry is committed in a given term, then that
\* entry will be present in the logs of the leaders
\* for all higher-numbered terms
\* See: https://github.com/uwplse/verdi-raft/blob/master/raft/LeaderCompletenessInterface.v
LeaderCompletenessInv == 
    \A i \in Server :
        LET committed == Committed(i) IN
        \A idx \in 1..Len(committed) :
            LET entry == log[i][idx] IN 
            \* if the entry is committed 
            \A l \in CurrentLeaders :
                \* all leaders with higher-number terms
                currentTerm[l] > entry.term =>
                \* have the entry at the same log position
                log[l][idx] = entry

\* Any entry committed by leader shall be persisted already
CommittedIsDurableInv ==
    \A i \in Server :
        state[i] = Leader => commitIndex[i] <= durableState[i].log

InvSequence == <<
    LogInv,
    MoreThanOneLeaderInv,
    ElectionSafetyInv,
    LogMatchingInv,
    QuorumLogInv,
    MoreUpToDateCorrectInv,
    LeaderCompletenessInv,
    CommittedIsDurableInv
>>

INV == Len(SelectSeqWithIdx(inv, LAMBDA x, y: ~x /\ y \notin netman.no_inv)) = 0
-----
(***************************************************************************
  State constraints
 ***************************************************************************)

\*CONSTANTS MaxSentMsgs,
\*          MaxRecvMsgs,
\*          MaxWireMsgs,
\*          MaxPartitionTimes,
\*          MaxCureTimes,
\*          MaxClientOperationsTimes,
\*          MaxAppenEntriesTimes,
\*          MaxElectionTimes,
\*          MaxLogLength,
\*          MaxTerm

CheckParameterHelper(n, p, Test(_,_)) ==
    IF p \in DOMAIN Parameters
    THEN Test(n, Parameters[p])
    ELSE TRUE
CheckParameterMax(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i <= j)

GetMaxTerm   == currentTerm[CHOOSE i \in Server: \A j \in Server: currentTerm[i] >= currentTerm[j]]

ScSent == CheckParameterMax(netman.n_sent, "MaxSentMsgs")       \*发送消息的次数上限
ScRecv == CheckParameterMax(netman.n_recv, "MaxRecvMsgs")       \*接收消息的次数上限
ScWire == CheckParameterMax(netman.n_wire, "MaxWireMsgs")       \*信道中存在的消息数量上限
ScTerm == CheckParameterMax(GetMaxTerm,    "MaxTerm")           \*任期上限
ScCure == CheckParameterMax(netman.n_cure, "MaxCureTimes")      \*节点恢复次数上限
ScPart == CheckParameterMax(netman.n_part, "MaxPartitionTimes") \*网络分区次数上限
ScElec == CheckParameterMax(netman.n_elec, "MaxElectionTimes")  \*发起选举次数上限
ScAe   == CheckParameterMax(netman.n_ae,   "MaxAppendEntriesTimes")  \*最多日志同步次数
ScOp   == CheckParameterMax(netman.n_op,   "MaxClientOperationsTimes")   \*最多用户操作次数
SC == /\ ScSent /\ ScRecv /\ ScWire /\ ScTerm /\ ScPart /\ ScElec /\ ScCure /\ ScAe /\ ScOp 

PrePrune(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

----
\* Network state transitions

\* The network duplicates a message
\* @type: MSG => Bool;
DuplicateMessage(m) ==
    /\ m \in DOMAIN msgs
    /\ msgs' = WithMessage(m, msgs)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>>

\* The network drops a message
\* @type: MSG => Bool;
DropMessage(m) ==
    \* Do not drop loopback msgs
    \* /\ m.src /= m.dst
    /\ Discard(m)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>>

----    
\* Defines how the variables may transition.
NextAsync == 
    /\ inv' = InvSequence
    /\  \/ /\ PrePrune(netman.n_sent, "MaxSentMsgs")
           /\ \E i,j \in Server : RequestVote(i, j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ /\ PrePrune(netman.n_op, "MaxClientOperationsTimes")
           /\ \E i \in Server: ClientRequest(i, 0)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ /\ PrePrune(netman.n_sent, "MaxSentMsgs")
           /\ \E i,j \in Server : \E b,e \in matchIndex[i][j]+1..Len(log[i])+1 : AppendEntries(i, j, <<b,e>>)
        \/ /\ PrePrune(netman.n_sent, "MaxSentMsgs")
           /\ \E i \in Server : AppendEntriesToSelf(i)
        \/ /\ PrePrune(netman.n_sent, "MaxSentMsgs")
           /\ \E i,j \in Server : Heartbeat(i, j)
        \/ /\ PrePrune(netman.n_sent, "MaxSentMsgs")
           /\ \E i,j \in Server : \E index \in 1..commitIndex[i] : SendSnapshot(i, j, index)
        \/ \E msrc, mdst \in Server:
            /\ LET m == NetGetMsg(msrc, mdst)
               IN /\ m /= Nil
                  /\ Receive(m)
        \/ /\ PrePrune(netman.n_elec, "MaxElectionTimes")
           /\ \E i \in Server : Timeout(i)
        \/ \E i \in Server : Ready(i)
        \* \/ \E i \in Server : StepDownToFollower(i)
        
NextCrash == /\ inv' = InvSequence
             /\ PrePrune(netman.n_cure, "MaxCureTimes")
             /\ \E i \in Server : Restart(i)

NextAsyncCrash ==
    \/ NextAsync
    \/ NextCrash

NextUnreliable ==    
    \* Only duplicate once
    \/ \E m \in DOMAIN msgs : 
        /\ msgs[m] = 1
        /\ DuplicateMessage(m)
    \* Only drop if it makes a difference            
    \/ \E m \in DOMAIN msgs : 
        /\ msgs[m] = 1
        /\ DropMessage(m)

\* Most pessimistic network model
Next == \/ NextAsync
        \* \/ NextCrash

\* Membership changes
NextDynamic ==
    \/ Next
    \/ \E i, j \in Server : AddNewServer(i, j)
    \/ \E i, j \in Server : AddLearner(i, j)
    \/ \E i, j \in Server : DeleteServer(i, j)
    \/ \E i \in Server : ApplySimpleConfChange(i)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
THEOREM Spec => []LogInv

===============================================================================



\* Changelog:
\* 
\* 2023-11-23:
\* - Replace configuration actions by those in etcd implementation.
\* - Refactor spec structure to decouple core spec and model checker spec for 
\*   better readness and future update
\* - Remove unused actions and properties, e.g. wrapper
\*  
\* 2021-04-??:
\* - Abandoned Apalache due to slowness and went back to TLC. There are remains
\*   of the Apalache-specific annotations and message wrapping/unwrapping, but
\*   those are not actually used. The annotations are no longer up-to-date. 
\*
\* 2021-04-09:
\* - Added type annotations for Apalache symbolic model checker. As part of
\*   this change, the message format was changed to a tagged union.
\* 
\* 2016-09-09:
\* - Daniel Ricketts added the major safety invariants and proved them in
\*   TLAPS.
\*
\* 2015-05-10:
\* - Add cluster membership changes as described in Section 4 of
\*     Diego Ongaro. Consensus: Bridging theory and practice.
\*     PhD thesis, Stanford University, 2014.
\*   This introduces: InitServer, ValueEntry, ConfigEntry, CatchupRequest,
\*     CatchupResponse, CheckOldConfig, GetMaxConfigIndex,
\*     GetConfig (parameterized), AddNewServer, DeleteServer,
\*     HandleCatchupRequest, HandleCatchupResponse,
\*     HandleCheckOldConfig 
\*
\* 
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation