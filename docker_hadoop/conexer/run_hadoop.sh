#!/bin/bash

#cp /usr/lib/hadoop/etc/hadoop/core-site.xml original_confs
#cp /usr/lib/hadoop/etc/hadoop/mapred-site.xml original_confs
#cp /usr/lib/hadoop/etc/hadoop/yarn-site.xml original_confs
#cp /usr/lib/hadoop/etc/hadoop/hdfs-site.xml original_confs

rm -rf gen_confs/*
# first copy default configurations back to Hadoop
cp hadoop_conf/* /localtmp/hadoop/hadoop-2.7.4/etc/hadoop

# then restart hadoop
# stop-all.sh
# start-all.sh

# while true;
# do
#         safemode=`hdfs dfsadmin -safemode get`
#     echo $safemode
#         if [ "$safemode" = "Safe mode is OFF" ]; then
#                 break
#         fi
#         sleep 1s
# done


# then prepare input data
../HiBench/bin/run_all.sh > /dev/null

#sudo cp hadoop_conf/* /usr/lib/hadoop/etc/hadoop
# then copy default configurations back to Hadoop
#cp hadoop_conf/* /localtmp/hadoop/hadoop-2.7.4/etc/hadoop

# execute exploration at last
cd src
python -u main.py 300
