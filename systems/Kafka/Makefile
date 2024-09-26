_replay_Kafka_series_bug:
	docker exec controller rm -rf /root/sandtable/systems/Kafka/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/Kafka/scripts/run_one_testcase.sh /root/sandtable/systems/Kafka/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/Kafka/bugs/${BUG_DIR}/test

replay_Kafka_election_safety_bug:
	make _replay_Kafka_series_bug BUG_DIR=leader_election N_SERVERS=3
	grep -r "become leader, term" build/mount/systems/Kafka/bugs/leader_election/test/log*