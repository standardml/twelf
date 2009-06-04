#!/bin/bash
# TWELF BUILD CONTROLLER
# Author: Robert J. Simmons
# 
# ./controller.sh [output-dir]
# Builds binary and source distributions, runs regressions, and puts
# output in the specifed directory (which is the current directory if no
# directory is specified)

# Change to my directory
cd `dirname $0`
export PATH=/usr/local/bin:$PATH:/opt/local/bin

# Parse destination directory
OUTPUT_DIR=$1
if [ -z "$OUTPUT_DIR" ] 
then OUTPUT_DIR=$PWD
fi

# Self Update
pushd .. >& /dev/null
svn -q update
popd >& /dev/null

#########################
# PART ONE: TWELF BUILD #
#########################

# Run build script
./build.sh $OUTPUT_DIR >& $OUTPUT_DIR/new-build-output
RETSTATUS=$?

# Attach new output to old output
pushd $OUTPUT_DIR >& /dev/null
touch build-output
mv build-output old-build-output
date | cat - new-build-output old-build-output > build-output

# Clean up
rm -f new-build-output
rm -f old-build-output
popd >& /dev/null

##############################
# PART TWO: TWELF REGRESSION #
##############################

# Run regression script
pushd "../TEST" >& /dev/null
./regression.sh full >& $OUTPUT_DIR/new-regression-output
popd >& /dev/null

# Attach new output to old output
pushd $OUTPUT_DIR > /dev/null
touch regression-output
mv regression-output old-regression-output
date | cat - new-regression-output old-regression-output > regression-output


# Clean up
rm -f new-regression-output
rm -f old-regression-output
popd >& /dev/null

