_replay_Etcd_series_bug:
	docker exec controller rm -rf /root/sandtable/systems/Etcd/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/Etcd/scripts/run_one_testcase.sh /root/sandtable/systems/Etcd/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/Etcd/bugs/${BUG_DIR}/test

replay_Etcd_election_safety_bug:
	make _replay_Etcd_series_bug BUG_DIR=leader_election N_SERVERS=3
	grep -r "become leader, term" build/mount/systems/Etcd/bugs/leader_election/test/log*