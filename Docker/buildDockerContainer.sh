#!/usr/bin/env bash

echo "Cloning into https://github.com/acorrenson/WiSE.git"
TMPDIR=$(mktemp -d)
echo "Temporary directory: $TMPDIR"
cd "$TMPDIR"
git clone -q https://github.com/acorrenson/WiSE.git
cd WiSE/

echo "Building Docker image"
vhash=$(docker build -q -t dsteinhoefel/wise .)

echo "Tagging image with hash $vhash to dsteinhoefel/wise:latest"
docker tag "$vhash" dsteinhoefel/wise:latest

cat << EOF

To deploy the built image to Docker Hub, run

  docker login

and enter your Docker Hub credentials. Afterward, run

  docker push dsteinhoefel/wise:latest

EOF
