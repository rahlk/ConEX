#!/bin/bash

N=11

# Stop hadoop master container
docker rm -f hadoop-master &> /dev/null

# Stop hadoop slave container
i=1
while [ $i -lt $N ]
do
	docker rm -f hadoop-worker$i &> /dev/null
done
