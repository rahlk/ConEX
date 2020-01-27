FROM ubuntu:18.04

MAINTAINER Rahul Krishna <i.m.ralk@gmail.com>

WORKDIR /root

#----- Install packages -----
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      openjdk-8-jdk       \
      git maven bc        \
      openssh-server wget \
      build-essential     \
      python2.7           \
      python2.7-dev       \
      python-pip &&       \
      pip install --upgrade pip virtualenv  && \
      apt-get clean  && \
      rm -rf /var/lib/apt/lists/*

#----- Install hadoop 2.7.4 -----
COPY hadoop-2.7.4.tar.gz hadoop-2.7.4.tar.gz
RUN tar -xf hadoop-2.7.4.tar.gz
RUN mv hadoop-2.7.4 /usr/local/hadoop-2.7.4
RUN rm hadoop-2.7.4.tar.gz

#----- Set environment variable -----
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
ENV HADOOP_HOME=/usr/local/hadoop-2.7.4
ENV PATH=$PATH:/usr/local/hadoop-2.7.4/bin:/usr/local/hadoop/sbin

#----- Passwordless ssh setup -----
RUN ssh-keygen -t rsa -f ~/.ssh/id_rsa -P '' && \
    cat ~/.ssh/id_rsa.pub >> ~/.ssh/authorized_keys

#----- Create DFS directories -----
RUN mkdir -p ~/hdfs/namenode && \
    mkdir -p ~/hdfs/datanode && \
    mkdir $HADOOP_HOME/logs

#----- Copy over config files -----
COPY config/* /tmp/

RUN mv /tmp/ssh_config ~/.ssh/config && \
    mv /tmp/hadoop-env.sh $HADOOP_HOME/etc/hadoop/hadoop-env.sh && \
    mv /tmp/hdfs-site.xml $HADOOP_HOME/etc/hadoop/hdfs-site.xml && \
    mv /tmp/core-site.xml $HADOOP_HOME/etc/hadoop/core-site.xml && \
    mv /tmp/mapred-site.xml $HADOOP_HOME/etc/hadoop/mapred-site.xml && \
    mv /tmp/yarn-site.xml $HADOOP_HOME/etc/hadoop/yarn-site.xml && \
    mv /tmp/slaves $HADOOP_HOME/etc/hadoop/slaves && \
    mv /tmp/start-hadoop.sh ~/start-hadoop.sh

COPY HiBench /root/HiBench

#----- Set new workdir to HiBench -----
WORKDIR /root/HiBench

#----- Build HiBench -----
RUN mvn -Phadoopbench clean package

RUN cp conf/hadoop.docker.conf.template conf/hadoop.conf

#---- Change permissions of Hadoop binaries -----
RUN chmod +x /root/start-hadoop.sh
RUN chmod +x $HADOOP_HOME/sbin/start-dfs.sh
RUN chmod +x $HADOOP_HOME/sbin/start-yarn.sh

#----- Format Namenode -----
RUN $HADOOP_HOME/bin/hdfs namenode -format

CMD [ "sh", "-c", "service ssh start; bash"]
