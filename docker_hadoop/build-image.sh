#!/bin/bash
echo "Getting docker image"
docker pull kiwenlau/hadoop:1.0

echo "Getting docker image"
docker network create --driver=bridge hadoop

echo -e "\nbuild docker hadoop image\n"
docker build -t kiwenlau/hadoop:1.0 .

echo ""
