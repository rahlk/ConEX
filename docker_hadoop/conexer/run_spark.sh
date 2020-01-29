#!/bin/bash

#cp /usr/lib/hadoop/etc/hadoop/core-site.xml original_confs
#cp /usr/lib/hadoop/etc/hadoop/mapred-site.xml original_confs
#cp /usr/lib/hadoop/etc/hadoop/yarn-site.xml original_confs
#cp /usr/lib/hadoop/etc/hadoop/hdfs-site.xml original_confs

# rm -rf gen_confs/*
# first copy default configurations back to Hadoop
# cp hadoop_conf/* /localtmp/hadoop/hadoop-2.7.4/etc/hadoop


# then prepare input data
# ../HiBench/bin/run_all.sh

#sudo cp hadoop_conf/* /usr/lib/hadoop/etc/hadoop
# then copy default configurations back to Hadoop
#cp hadoop_conf/* /localtmp/hadoop/hadoop-2.7.4/etc/hadoop

# execute exploration at last
cp /localtmp/chong/spark-defaults.conf /localtmp/spark-2.2.0/conf/
cd src
python -u initializer.py
