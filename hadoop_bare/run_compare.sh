#!/usr/bin/sh

# Make a local copy of the default hadoop configurations

# Copy over the HiBench config
docker cp config/benchmarks.lst hadoop-master:/root/HiBench/conf/ && \
docker cp config/frameworks.lst hadoop-master:/root/HiBench/conf/ && \
docker cp config/hibench.conf    hadoop-master:/root/HiBench/conf/

# Loop through every folder
for d in results/*/
do 
  # -- Copy over all the configurations to the master node --
  for f in $d/*.xml
  do
    docker cp $f hadoop-master:/usr/local/hadoop-2.7.4/etc/hadoop/
  done
  # -- Run HiBench and gather the runtime --
  docker exec -it hadoop-master /root/HiBench/bin/run_all.sh
  docker exec -it hadoop-master cat /root/HiBench/report/wordcount/hadoopbench.log | grep 'CPU time spent' | sed 's/\t//g' | tee scale_up_runtimes.txt
done 
