#!/bin/bash

source $(dirname "$(realpath "$0")")/env.sh
source $START_DOCKER_COMMON_SH "$@"

CLIENT=$(pwd)/../kafka_2.12-3.7.0/bin/start.sh

HOST_CMD="-r 'sudo timeout --foreground $TIMEOUT $CONTROLLER -detail -config $CONFIG_FILE -tmpdir $TMPDIR -half_duplex_connection; exit'"

cat <<EOF | eval "$SPSSH_SH" -H -S -b -q -t -e -s $HOST_CMD -w "$TMPDIR" $TIMEOUT_ARG root@n{1,2,3}
cd $TESTCASE_DIR
export PROGRAM_PATH=/usr/bin/java
$INTERCEPTOR_SH -config $CONFIG_FILE $CLIENT $CONFIG_FILE; exit
EOF

source $WAIT_TMUX_COMMON_SH