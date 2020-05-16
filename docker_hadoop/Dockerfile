FROM ubuntu:18.04

LABEL maintainer="Rahul Krishna <i.m.ralk@gmail.com>"

WORKDIR /root

#----- Install packages -----
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
  ocaml opam m4\
  vim \
  curl \
  openjdk-8-jdk       \
  git maven bc        \
  openssh-server wget \
  build-essential     \
  python-setuptools   \
  python2.7           \
  python2.7-dev       \
  python-pip &&       \
  pip install --upgrade pip virtualenv  && \
  apt-get clean  && \
  rm -rf /var/lib/apt/lists/*

# ----- This for debug only -----
RUN wget -O ~/.vimrc https://gist.githubusercontent.com/rahlk/78d3d8f188a099dfd5114c35176e391d/raw/ed47d4fee79b5e177cb008abb319ebe4b542fc75/.vimrc

#----- Install hadoop 2.7.4 -----
RUN wget -O hadoop-2.7.4.tar.gz https://archive.apache.org/dist/hadoop/core/hadoop-2.7.4/hadoop-2.7.4.tar.gz
RUN tar -xf hadoop-2.7.4.tar.gz
RUN mv hadoop-2.7.4 /usr/local/hadoop-2.7.4
RUN rm hadoop-2.7.4.tar.gz

#----- Install COQ Proof checher -----
RUN opam init -a
RUN eval `opam config env`
# Pin the coq package to version 8.7.2 and install it.
RUN opam pin add coq 8.7.2 --yes


#----- Set environment variable -----
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
ENV HADOOP_HOME=/usr/local/hadoop-2.7.4
ENV PATH=$PATH:/usr/local/hadoop-2.7.4/bin:/usr/local/hadoop/sbin:/root/.opam/system/bin
ENV PYTHONDONTWRITEBYTECODE=1

#----- Passwordless ssh setup -----
RUN ssh-keygen -t rsa -f ~/.ssh/id_rsa -P '' && \
  cat ~/.ssh/id_rsa.pub >> ~/.ssh/authorized_keys

#----- Create DFS directories -----
RUN mkdir -p ~/hdfs/namenode && \
  mkdir -p ~/hdfs/datanode && \
  mkdir $HADOOP_HOME/logs

#----- Copy over config files -----
COPY ./config* /tmp/

#----- Mount HiBench -----
RUN git clone https://github.com/Intel-bigdata/HiBench /root/HiBench

RUN mv /tmp/ssh_config ~/.ssh/config && \
  mv /tmp/slaves $HADOOP_HOME/etc/hadoop/slaves && \
  mv /tmp/hadoop-env.sh $HADOOP_HOME/etc/hadoop/hadoop-env.sh && \
  mv /tmp/hdfs-site.xml $HADOOP_HOME/etc/hadoop/hdfs-site.xml && \
  mv /tmp/core-site.xml $HADOOP_HOME/etc/hadoop/core-site.xml && \
  mv /tmp/mapred-site.xml $HADOOP_HOME/etc/hadoop/mapred-site.xml && \
  mv /tmp/yarn-site.xml $HADOOP_HOME/etc/hadoop/yarn-site.xml && \
  mv /tmp/hadoop.conf /root/HiBench/conf && \
  mv /tmp/frameworks.lst /root/HiBench/conf && \
  mv /tmp/benchmarks.lst /root/HiBench/conf && \
  mv /tmp/hibench.conf /root/HiBench/conf && \
  mv /tmp/start-hadoop.sh ~/start-hadoop.sh

#----- Clone lastest ConEX code -----
RUN git config --global user.name "rahlk" && \
  git config --global user.email "i.m.ralk@gmail.com" && \
  git clone https://github.com/rahlk/conexer /root/conexer

#----- Install python dependencies -----
WORKDIR /root/conexer
RUN pip install -r requirements.txt

#----- Set new workdir to HiBench -----
WORKDIR /root/HiBench

#----- Build HiBench -----
RUN mvn -Phadoopbench clean package

#----- Set new workdir to root -----
WORKDIR /root

#---- Change permissions of Hadoop binaries -----
RUN chmod +x /root/start-hadoop.sh
RUN chmod +x $HADOOP_HOME/sbin/start-dfs.sh
RUN chmod +x $HADOOP_HOME/sbin/start-yarn.sh

#----- Format Namenode -----
RUN $HADOOP_HOME/bin/hdfs namenode -format

CMD [ "sh", "-c", "service ssh start; bash"]
