#!/bin/bash

DIRS=`find . -type d -depth 1 | grep -v ".svn"`

for DIR in $DIRS 
do
    cd $DIR
    ln -s ../Makefile.sub ./Makefile
    cd ..
done
