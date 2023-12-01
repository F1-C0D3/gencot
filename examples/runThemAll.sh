#!/bin/sh

echo "Running Example helloworld"
echo "=========================="
cd helloworld
make cogent-run
make clean
cd ..

echo "Running Example cards"
echo "====================="
cd cards
make cogent-run
make clean
cd ..

echo "Running Example cards2"
echo "======================"
cd cards2
make UNIT=part cogent-run
make UNIT=part clean
make cogent-run
make clean
cd ..

echo "Running Example types"
echo "====================="
cd types
make cogent-binary
make clean
cd ..

echo "Running Example items"
echo "====================="
cd items
make cogent-run
make clean
cd ..

