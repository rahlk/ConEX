#!/bin/bash
echo "Getting docker image"
sudo docker pull kiwenlau/hadoop:1.0

echo "Getting docker image"
sudo docker network create --driver=bridge hadoop

echo -e "\nbuild docker hadoop image\n"
sudo docker build -t kiwenlau/hadoop:1.0 .

echo ""
