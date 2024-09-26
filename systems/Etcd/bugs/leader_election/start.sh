#!/bin/bash

#set -xe

RUN_SH_DIR=$(dirname "$(realpath "$0")")
CURRENT_DIR=$(realpath .)

dns_prefix=n
dns_suffix=

myid=$SSH_NO

if [ -z "$myid" ]; then
    echo SSH_NO is not set
    exit 1
fi

CONFIG_FILE=$1

if [ -z "$CONFIG_FILE" ]; then
    echo CONFIG_FILE is not set
    exit
fi

if [ "$2" = "real-addr" ]; then
    REAL_ADDR=1
fi

SCRIPT_DIR=$(dirname "$(realpath "$0")")
server_dir="$CURRENT_DIR/data/$myid"

mkdir -p "$server_dir"
echo $myid > "$server_dir/myid"

FLE_MIN_NOT=200
FLE_MAX_NOT=210

rm -rf /tmp/kraft-controller-logs/*

config_file="$server_dir/config.cfg"

#nodes=($(dig +short n{1,2,3} | sed "$(sed -En -e 's,.0/24,,g' -e 's/map-cidr (.*) (.*)/s,\2,\1,g/p' $CONFIG_FILE)"))
exec $CURRENT_DIR/../etcd --name n${myid} --listen-client-urls http://10.255.255.10${myid}:9080 --advertise-client-urls http://10.255.255.10${myid}:9081 --listen-peer-urls http://10.255.255.10${myid}:9084 --initial-advertise-peer-urls http://10.255.255.10${myid}:9084 --initial-cluster-token etcd-cluster-1 --initial-cluster 'n1=http://10.255.255.101:9084,n2=http://10.255.255.102:9084,n3=http://10.255.255.103:9084' --initial-cluster-state new --enable-pprof --logger=zap --log-outputs=stderr
# exec $CURRENT_DIR/../etcd --name n${myid} --listen-client-urls http://10.255.255.10${myid}:9080 --advertise-client-urls http://10.255.255.10${myid}:9081 --listen-peer-urls http://10.255.255.10${myid}:9082 --initial-advertise-peer-urls http://10.255.255.10${myid}:9083 --initial-cluster-token etcd-cluster-1 --initial-cluster 'n1=http://10.255.255.101:9083,n2=http://10.255.255.102:9083,n3=http://10.255.255.103:9083' --initial-cluster-state new --enable-pprof --logger=zap --log-outputs=stderr
# etcd --name infra1 --listen-client-urls http://127.0.0.1:12379 --advertise-client-urls http://127.0.0.1:12379 --listen-peer-urls http://127.0.0.1:12380 --initial-advertise-peer-urls http://127.0.0.1:12380 --initial-cluster-token etcd-cluster-1 --initial-cluster 'infra1=http://127.0.0.1:12380,infra2=http://127.0.0.1:22380,infra3=http://127.0.0.1:32380' --initial-cluster-state new --enable-pprof --logger=zap --log-outputs=stderr