#!/bin/sh
rm -rf binary
mkdir binary
cd code/yalsat
./configure.sh -O || exit 1
make || exit 1
cd ../plingeling
./configure.sh || exit 1
make plingeling || exit 1
install -m 755 -s plingeling ../../binary
