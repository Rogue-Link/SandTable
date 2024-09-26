----------------------------- MODULE Kafka -----------------------------

EXTENDS Sequences, Naturals, Integers, FiniteSets, TLC

(***************************************************************************
  Constants definitions
 ***************************************************************************)
CONSTANTS Server                       \* Server set
CONSTANTS Follower, Candidate, Leader, Unattached, Voted  \* Server states
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          BeginQuorumRequest, BeginQuorumResponse,
          EndQuorumRequest           \* Raft message types
CONSTANTS Parameters, Nil  \* Misc: state constraint parameters and placeholder
\* Errors
CONSTANTS FencedLeaderEpoch, NotLeader, UnknownLeader
\* Special state that indicates a server has entered an illegal state
CONSTANTS IllegalState       
\* Used for filtering messages under different circumstances
CONSTANTS AnyEpoch, EqualEpoch

(***************************************************************************
  Variables definitions
 ***************************************************************************)
VARIABLES currentEpoch, votedFor, leader, state, pendingFetch  \* Persistent variables
VARIABLES votesGranted, msgs                 \* Candidate variables

(***************************************************************************
  Network variables and instance
 ***************************************************************************)
VARIABLES netman, netcmd
VARIABLES requestQueue
INSTANCE FifoNetwork WITH FLUSH_DISCONN <- TRUE, NULL_MSG <- Nil,
    _msgs <- msgs, _netman <- netman, _netcmd <- netcmd

(***************************************************************************
  Self manipulated invariants checking
 ***************************************************************************)
VARIABLES inv
VARIABLES normal_act, error_act

serverVars == <<currentEpoch, state, votedFor, leader, pendingFetch>>
candidateVars == <<votesGranted, requestQueue>>
actVars       == <<normal_act, error_act>>
netVars       == <<netman, netcmd, msgs>>
noNetVars     == <<serverVars, candidateVars>>
vars          == <<noNetVars, netVars, inv, actVars>>

(***************************************************************************
  Type Ok
 ***************************************************************************)
TypeOkServerVars ==
    /\ currentEpoch \in [ Server -> Nat ]
    /\ votedFor    \in [ Server -> Server \cup {Nil} ]
    /\ leader   \in [ Server -> Server \cup {Nil} ]
    /\ state   \in [ Server -> { Follower, Candidate, Leader, Unattached, Voted } ]
    /\ pendingFetch \in [ Server -> Server \cup {Nil} ]
    /\ normal_act \in Nat
    /\ error_act \in Nat

TypeOk ==
    /\ TypeOkServerVars

(***************************************************************************
  Init variables
 ***************************************************************************)
GetParameterSet(p)  == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE {}

InitServerVars == /\ currentEpoch = [i \in Server |-> 1]
                  /\ state        = [i \in Server |-> Unattached]
                  /\ leader       = [i \in Server |-> Nil]
                  /\ votedFor     = [i \in Server |-> Nil]
                  /\ pendingFetch = [i \in Server |-> Nil]
                  /\ requestQueue = [i \in Server |-> [j \in Server |-> {}]]
InitCandidateVars == /\ votesGranted = [i \in Server |-> {}]
InitActVars == /\ normal_act = 0
               /\ error_act = 0
InitInv == inv = <<>>

Init == /\ InitServerVars
        /\ InitCandidateVars
        /\ InitActVars
        /\ InitFifoNetworkAddNetman(Server, <<"init", Cardinality(Server)>>, 
            [ n_op |-> 0, n_ae |-> 0, n_elec |-> 0, no_inv |-> GetParameterSet("NoInv")])
        /\ InitInv

(***************************************************************************
  Helper functions
 ***************************************************************************)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The epoch of the last entry in a log, or 0 if the log is empty.
LastEpoch(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].epoch

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

MinEpo(s) == CHOOSE x \in s: \A y \in s : x.epoch <= y.epoch

\* Compares two entries, with epoch taking precedence. 
\* Offset only matters when both have the same epoch.
\* When entry1 > entry2 then 1
\* When entry1 = entry2 then 0
\* When entry1 < entry2 then 1
CompareEntries(offset1, epoch1, offset2, epoch2) ==
    CASE epoch1 > epoch2 -> 1
      [] epoch1 = epoch2 /\ offset1 > offset2 -> 1
      [] epoch1 = epoch2 /\ offset1 = offset2 -> 0
      [] OTHER -> -1


\* Transition helpers ------------------------------

\* TRUE if server i and the peer have a consistent view on leadership,
\* FALSE if not.
HasConsistentLeader(i, leaderId, epoch) ==
    IF leaderId = i
    THEN \* if the peer thinks I am leader, and I am really leader
         \* then TRUE, else FALSE
         state[i] = Leader
    ELSE \* either the peer doesn't know there is a leader, or this
         \* node doesn't know a leader, or both agree on the same leader,
         \* or they have different epochs
         \/ epoch # currentEpoch[i]
         \/ leaderId = Nil
         \/ leader[i] = Nil
         \/ leader[i] = leaderId

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i], i)
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

SetIllegalState ==
    [state |-> IllegalState, epoch |-> 0, leader |-> Nil]

NoTransition(i) ==
    [state |-> state[i], epoch |-> currentEpoch[i], leader |-> leader[i]]

TransitionToVoted(i, epoch, state0) ==
    IF /\ state0.epoch = epoch
       /\ state0.state # Unattached
    THEN SetIllegalState
    ELSE [state |-> Voted, epoch |-> epoch, leader |-> Nil]

TransitionToUnattached(epoch) ==
    [state |-> Unattached, epoch |-> epoch, leader |-> Nil]
    
TransitionToFollower(i, leaderId, epoch) ==
    IF /\ currentEpoch[i] = epoch
       /\ \/ state[i] = Follower
          \/ state[i] = Leader
    THEN SetIllegalState
    ELSE [state |-> Follower, epoch |-> epoch, leader |-> leaderId]
    
MaybeTransition(i, leaderId, epoch) ==
    CASE ~HasConsistentLeader(i, leaderId, epoch) ->
            SetIllegalState
      [] epoch > currentEpoch[i] ->
            \* the epoch of the node is stale, become a follower
            \* if the request contained the leader id, else become
            \* unattached
            IF leaderId = Nil
            THEN TransitionToUnattached(epoch)
            ELSE TransitionToFollower(i, leaderId, epoch)
      [] leaderId # Nil /\ leader[i] = Nil ->
            \* the request contained a leader id and this node does not know
            \* of a leader, so become a follower of that leader
            TransitionToFollower(i, leaderId, epoch)
      [] OTHER ->
            \* no changes
            NoTransition(i)

MaybeHandleCommonResponse(i, leaderId, epoch, errors) ==
    CASE epoch < currentEpoch[i] ->
                \* stale epoch, do nothing
                [state |-> state[i],
                 epoch |-> currentEpoch[i],
                 leader |-> leader[i],
                 handled |-> TRUE]
      [] epoch > currentEpoch[i] \/ errors # Nil ->
                \* higher epoch or an error
                MaybeTransition(i, leaderId, epoch) @@ [handled |-> TRUE]
      [] /\ epoch = currentEpoch[i]
         /\ leaderId # Nil
         /\ leader[i] = Nil ->
                \* become a follower
                [state   |-> Follower, 
                 leader  |-> leaderId,
                 epoch   |-> currentEpoch[i],
                 handled |-> TRUE]
      [] OTHER -> 
                \* no changes to state or leadership
                [state   |-> state[i],
                 epoch   |-> currentEpoch[i], 
                 leader  |-> leader[i],
                 handled |-> FALSE]
             
HandleAct ==
    CASE normal_act < 4 * error_act -> FALSE
      [] OTHER -> TRUE

(***************************************************************************)
(*   Raft message handling                                                 *)
(***************************************************************************)

RequestVote(i) ==
    /\ state[i] \in {Follower, Candidate, Unattached}
    /\ state'        = [state EXCEPT ![i] = Candidate]
    /\ currentEpoch' = [currentEpoch EXCEPT ![i] = currentEpoch[i] + 1]
    /\ leader'       = [leader EXCEPT ![i] = Nil]
    /\ votedFor'     = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
    /\ LET xy == Server \ {i}
           x == CHOOSE j \in xy: TRUE
           y == CHOOSE j \in xy: j # x
           m1 == [ src  |-> i, dst |-> x, type |-> RequestVoteRequest,
                                           mepoch |-> currentEpoch'[i]]
           m2 == [ src  |-> i, dst |-> y, type |-> RequestVoteRequest,
                                           mepoch |-> currentEpoch'[i]]
       IN /\ IF Cardinality(requestQueue[i][x]) # 0 \/ Cardinality(requestQueue[i][y]) # 0
             THEN IF Cardinality(requestQueue[i][x]) # 0 /\ Cardinality(requestQueue[i][y]) # 0
                  THEN /\ requestQueue[i][x]' = requestQueue[i][x] \cup m1
                       /\ requestQueue[i][y]' = requestQueue[i][y] \cup m2
                       /\ UNCHANGED <<netVars>>
                  ELSE IF Cardinality(requestQueue[i][x]) # 0
                       THEN /\requestQueue[i][y]' = requestQueue[i][y] \cup m2
                            /\ NetUpdate2(NetmanIncField("n_elec", NetAddMsg(m1)), <<"ElectionTimeout only one", i>>)
                       ELSE /\requestQueue[i][x]' = requestQueue[i][x] \cup m1
                            /\ NetUpdate2(NetmanIncField("n_elec", NetAddMsg(m2)), <<"ElectionTimeout only one", i>>)
             ELSE LET dsts == Server \ {i}
                      size == Cardinality(dsts)
                      F[n \in 0..size] ==
                           IF n = 0 THEN <<<<>>, dsts>>
                           ELSE LET ms == F[n-1][1]
                                    s == CHOOSE j \in F[n-1][2]: TRUE
                                    m == [ src  |-> i, dst |-> s, type |-> RequestVoteRequest,
                                           mepoch |-> currentEpoch'[i]]
                                    remaining == F[n-1][2] \ {s}
                                IN <<Append(ms, m), remaining>>
                  IN /\ NetUpdate2(NetmanIncField("n_elec", NetBatchAddMsg(F[size][1])), <<"ElectionTimeout", i>>)
                     /\ Assert(Cardinality(F[size][2]) = 0, <<"ElectionTimeout bug", F>>)
                     /\ UNCHANGED <<requestQueue>>
               
HandleRequestVoteRequest(m) ==
            LET i     == m.dst
               j     == m.src
               error    == IF m.mepoch < currentEpoch[i]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               state0   == IF m.mepoch > currentEpoch[i]
                           THEN TransitionToUnattached(m.mepoch)
                           ELSE NoTransition(i)
               grant == /\ \/ state0.state = Unattached
                           \/ /\ state0.state = Voted
                              /\ votedFor[i] = j
               finalState == IF grant /\ state0.state = Unattached
                             THEN TransitionToVoted(i, m.mepoch, state0)
                             ELSE state0                         
            IN /\ IF error = Nil
                  THEN
                       /\ state' = [state EXCEPT ![i] = finalState.state]
                       /\ currentEpoch' = [currentEpoch EXCEPT ![i] = finalState.epoch]
                       /\ leader' = [leader EXCEPT ![i] = finalState.leader]
                       /\ \/ /\ grant
                             /\ votedFor' = [votedFor EXCEPT ![i] = j]
                          \/ /\ ~grant
                             /\ UNCHANGED votedFor
                       /\ IF state # state'
                          THEN /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
                               /\ requestQueue' = [requestQueue EXCEPT ![i] = [p \in Server |-> {}]]
                          ELSE UNCHANGED <<pendingFetch, requestQueue>>
                       /\ LET reply1 == [type   |-> RequestVoteResponse,
                                mepoch        |-> m.mepoch,
                                mleader       |-> finalState.leader,
                                mvoteGranted  |-> grant,
                                merror        |-> Nil,
                                src       |-> i,
                                dst         |-> j]
                          IN  NetUpdate2(NetReplyMsg(reply1, m), <<"HandleMsgRV", "voted", i, j>>)
                  ELSE /\ LET reply2 == [type    |-> RequestVoteResponse,
                                mepoch        |-> currentEpoch[i],
                                mleader       |-> leader[i],
                                mvoteGranted  |-> FALSE,
                                merror        |-> error,
                                src       |-> i,
                                dst         |-> j]
                          IN  NetUpdate2(NetReplyMsg(reply2, m), <<"HandleMsgRV", "not-voted", i, j>>)
                       /\ UNCHANGED << serverVars, requestQueue>>
               /\ UNCHANGED <<candidateVars, requestQueue>>

                       

HandleRequestVoteResponse(m) ==
        /\ LET i        == m.dst
               j        == m.src
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ IF newState.handled = TRUE
                 THEN /\ state' = [state EXCEPT ![i] = newState.state]
                      /\ leader' = [leader EXCEPT ![i] = newState.leader]
                      /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
                      /\ IF state' # state
                         THEN /\ requestQueue' = [requestQueue EXCEPT ![i] = [p \in Server |-> {}]]
                              /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "not-candidate-or-term-not-equal", i, j>>)
                              /\ UNCHANGED <<votesGranted>>
                         ELSE IF Cardinality(requestQueue[i][j]) = 0
                              THEN /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "not-candidate-or-term-not-equal", i, j>>)
                                   /\ UNCHANGED <<votesGranted, requestQueue>>
                              ELSE LET reply == MinEpo(requestQueue[i][j]) 
                                       remain == requestQueue[i][j] \ reply
                                   IN /\ NetUpdate2(NetReplyMsg(reply, m), <<"HandleMsgRVR", "not-candidate-or-term-not-equal", i, j>>)
                                      /\ requestQueue[i][j]' = remain
                 ELSE
                      /\ state[i] = Candidate
                      /\ \/ /\ m.mvoteGranted
                            /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                      votesGranted[i] \cup {j}]
                            /\ IF votesGranted'[i] \in Quorum
                               THEN /\ state'  = [state EXCEPT ![i] = Leader]
                                    /\ leader' = [leader EXCEPT ![i] = i]
                                    /\ IF votesGranted'[i] = Server
                                       THEN LET dsts == Server \ {i}
                                                size == Cardinality(dsts)
                                                F[n \in 0..size] ==
                                                        IF n = 0 THEN <<<<>>, dsts>>
                                                        ELSE LET ms == F[n-1][1]
                                                                s == CHOOSE x \in F[n-1][2]: TRUE
                                                                msg == [ src |-> i, dst |-> s, type |-> BeginQuorumRequest,
                                                                        mepoch |-> currentEpoch[i] ]
                                                                remaining == F[n-1][2] \ {s}
                                                             IN <<Append(ms, msg), remaining>>
                                            IN /\ NetUpdate2(NetReplyBatchAddMsg(F[size][1], m), <<"HandleMsgRVR", "accept-all-and-beginQuorum", i>>)
                                               /\ Assert(Cardinality(F[size][2]) = 0, <<"BeginQuorum bug", F>>)
                                       ELSE LET sin_reply == [src |-> i, dst |-> j, type |-> BeginQuorumRequest,
                                                                        mepoch |-> currentEpoch[i]]
                                            IN NetUpdate2(NetReplyMsg(sin_reply, m), <<"HandleMsgRVR", "accept-one-and-beginQuorum", i, j>>)
                               ELSE UNCHANGED <<state, leader, netVars>>
                         \/ /\ ~m.mvoteGranted
                            /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "reject", i, j>>)
                            /\ UNCHANGED <<votesGranted, state, leader>>
                      /\ UNCHANGED <<currentEpoch, requestQueue>>
              /\ UNCHANGED <<votedFor, pendingFetch>>                  

HandleBeginQuorumRequest(m) ==
        /\ LET i        == m.dst
               j        == m.src
               error    == IF m.mepoch < currentEpoch[i]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               newState == MaybeTransition(i, m.src, m.mepoch)
           IN IF error = Nil
              THEN
                   /\ state' = [state EXCEPT ![i] = newState.state]
                   /\ leader' = [leader EXCEPT ![i] = newState.leader]
                   /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
                   /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
                   /\ LET reply1 == [type      |-> BeginQuorumResponse,
                             mepoch     |-> m.mepoch,
                             src    |-> i,
                             dst      |-> j,
                             merror     |-> Nil]
                      IN NetUpdate2(NetReplyMsg(reply1, m), <<"HandleMsgBQ", "noerror", i, j>>)
              ELSE /\ LET reply2 == [type      |-> BeginQuorumResponse,
                             mepoch     |-> currentEpoch[i],
                             src    |-> i,
                             dst      |-> j,
                             merror     |-> error]
                      IN NetUpdate2(NetReplyMsg(reply2, m), <<"HandleMsgBQ", "error", i, j>>)
                   /\ UNCHANGED <<state, leader, currentEpoch, pendingFetch>>
        /\ UNCHANGED <<votedFor, candidateVars>>

HandleBeginQuorumResponse(m) ==
    /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgBQR", "get", m.dst, m.src>>)
    /\ UNCHANGED <<noNetVars, requestQueue>>


(***************************************************************************
  Invariants
 ***************************************************************************)
NoIllegalState ==
    ~\E i \in Server :
        state[i] = IllegalState

NeverTwoLeadersInSameEpoch ==    
    ~\E i, j \in Server :
        /\ leader[i] # Nil
        /\ leader[j] # Nil
        /\ leader[i] # leader[j]
        /\ currentEpoch[i] = currentEpoch[j]
VotedState ==
    ~\E i \in Server : 
        /\ leader[i] = i
        /\ votedFor[i] # Nil
        
InvSequence == <<
    NoIllegalState,
    NeverTwoLeadersInSameEpoch
>>

INV == Len(SelectSeqWithIdx(inv, LAMBDA x, y: ~x /\ y \notin netman.no_inv)) = 0

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

GetMaxTerm   == currentEpoch[CHOOSE i \in Server: \A j \in Server: currentEpoch[i] >= currentEpoch[j]]

ScSent == CheckParameterMax(netman.n_sent, "MaxSentMsgs")       \*发送消息的次数上限
ScRecv == CheckParameterMax(netman.n_recv, "MaxRecvMsgs")       \*接收消息的次数上限
ScWire == CheckParameterMax(netman.n_wire, "MaxWireMsgs")       \*信道中存在的消息数量上限
ScTerm == CheckParameterMax(GetMaxTerm,    "MaxTerm")           \*任期上限
ScCure == CheckParameterMax(netman.n_cure, "MaxCureTimes")      \*节点恢复次数上限
ScPart == CheckParameterMax(netman.n_part, "MaxPartitionTimes") \*网络分区次数上限
ScElec == CheckParameterMax(netman.n_elec, "MaxElectionTimes")  \*发起选举次数上限

SC == /\ ScSent /\ ScRecv /\ ScWire /\ ScTerm /\ ScPart /\ ScElec /\ ScCure
      
PrePrune(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

 (***************************************************************************
  Next actions
 ***************************************************************************)
DoHandleMsgRV ==
    /\ \E src, dst \in Server:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = RequestVoteRequest
              /\ HandleRequestVoteRequest(m)
    /\ inv' = InvSequence

DoHandleMsgRVR ==
    /\ \E src \in Server, dst \in Server:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = RequestVoteResponse
              /\ HandleRequestVoteResponse(m)
    /\ inv' = InvSequence
    
DoHandleMsgBQ ==
    /\ \E src \in Server, dst \in Server:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = BeginQuorumRequest
              /\ HandleBeginQuorumRequest(m)
    /\ inv' = InvSequence
    
DoHandleMsgBQR ==
    /\ \E src \in Server, dst \in Server:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = BeginQuorumResponse
              /\ HandleBeginQuorumResponse(m)
    /\ inv' = InvSequence

DoElectionTimeout ==
    /\ PrePrune(netman.n_elec, "MaxElectionTimes")
    /\ \E n \in Server: state[n] # Leader /\ RequestVote(n)
    /\ inv' = InvSequence

DoNetworkPartition ==
    /\ PrePrune(netman.n_part, "MaxPartitionTimes")
    /\ \E n \in Server:
        /\ NetUpdate2(NetPartConn({n}), <<"DoNetworkPartition", n>>)
        /\ UNCHANGED noNetVars
    /\ inv' = InvSequence

DoNetworkCure ==
    /\ PrePrune(netman.n_cure, "MaxCureTimes")
    /\ NetIsParted
    /\ NetUpdate2(NetCureConn, <<"DoNetworkCure">>)
    /\ UNCHANGED noNetVars
    /\ inv' = InvSequence


\*Next ==    \/ DoElectionTimeout
\*           \/ DoHandleMsgRV
\*           \/ DoHandleMsgRVR
\*           \/ DoHandleMsgBQ
\*           \/ DoHandleMsgBQR
\*           \/ DoNetworkPartition
\*           \/ DoNetworkCure

Next == IF HandleAct
        THEN \/ /\ normal_act' = normal_act + 1
                /\ UNCHANGED <<error_act>>
                /\ \/ DoHandleMsgRV
                   \/ DoHandleMsgRVR
                   \/ DoHandleMsgBQ
                   \/ DoHandleMsgBQR
                   \/ DoHandleMsgRV
             \/ /\ error_act' = error_act + 1
                /\ UNCHANGED <<normal_act>>
                /\ \/ DoElectionTimeout
                   \/ DoNetworkPartition
                   \/ DoNetworkCure
        ELSE /\ normal_act' = normal_act + 1
             /\ UNCHANGED <<error_act>>
             /\ \/ DoHandleMsgRV
                \/ DoHandleMsgRVR
                \/ DoHandleMsgBQ
                \/ DoHandleMsgBQR

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon Jul 01 15:54:29 CST 2024 by chengjunhui