#!/bin/bash

# the default node number is 3
N=8

# start hadoop master container
sudo docker rm -f hadoop-master &> /dev/null
echo "Starting hadoop-master container..."
sudo docker run -itd \
                --net=hadoop \
                -p 50070:50070 \
                -p 8088:8088 \
                --name hadoop-master \
                --hostname hadoop-master \
                kiwenlau/hadoop:1.0 &> /dev/null


# start hadoop slave container
i=0
while [ $i -lt $N ]
do
	sudo docker rm -f hadoop-worker$i &> /dev/null
	echo "Starting hadoop-worker$i container..."
	sudo docker run -itd \
	                --net=hadoop \
	                --name hadoop-worker$i \
	                --hostname hadoop-worker$i \
	                kiwenlau/hadoop:1.0 &> /dev/null
	i=$(( $i + 1 ))
done

# -- Start hadoop --
echo "Starting DFS and YARN..."
docker exec -it hadoop-master /root/start-hadoop.sh > /dev/null

# -- Prepare HiBench data --
echo "Starting ConEX on Hadoop..."
docker exec -it hadoop-master conexer/run_hadoop.sh

# # -- Run HiBench Benchmark --
# echo "Running HiBench Benchmark..."
# docker exec -it hadoop-master bin/workloads/micro/wordcount/hadoop/run.sh > /dev/null
# # -- Print the report --
# echo ""
# docker exec -it hadoop-master cat report/hibench.report
