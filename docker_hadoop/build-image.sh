#!/bin/bash
echo "Getting docker image"
docker pull ubuntu:latest

echo "Getting docker image"
docker network create --driver=bridge hadoop

echo -e "\nbuild docker hadoop image\n"
docker build -t ubuntu:latest .

echo ""
