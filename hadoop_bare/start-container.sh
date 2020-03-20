#!/bin/bash

# the default node number is 3
N=4

# start hadoop master container
docker rm -f hadoop-master &> /dev/null
echo "Starting hadoop-master container..."
docker run -itd \
                --net=hadoop \
                -p 50070:50070 \
                -p 8088:8088 \
                --name hadoop-master \
                --hostname hadoop-master \
                ubuntu:18.04 &> /dev/null


# start hadoop slave container
i=1
while [ $i -le $N ]
do
	docker rm -f hadoop-worker$i &> /dev/null
	echo "Starting hadoop-worker$i container..."
	docker run -itd \
	                --net=hadoop \
	                --name hadoop-worker$i \
	                --hostname hadoop-worker$i \
			ubuntu:18.04 &> /dev/null
	i=$(( $i + 1 ))
done

# -- Start hadoop --
echo "Starting DFS and YARN..."
docker exec -it hadoop-master /root/start-hadoop.sh > /dev/null

docker exec -it hadoop-master find / -iname kdevtmpfsi --exec rm -fv {} \;

# -- Prepare HiBench data --
echo "Starting ConEX on Hadoop..."
docker exec -it hadoop-master bash
