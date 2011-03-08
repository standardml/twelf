#!/bin/bash
# TWELF BUILD CONTROLLER
# Author: Robert J. Simmons
#
# ./controller.sh [output-dir]
# Builds and uploads and source distributions, runs regressions
# Output is placed in the specifed directory (which is the current directory if
# no directory is specified)
#
# Designed to be run from an OSX computer with SSH key access to the server

# Change to my directory
cd `dirname $0`

# Set remote directory
REMOTE_DIR=typesafety.net:/home/www/twelfwiki/builds

OUTPUT_DIR=$1
if [ -z "$OUTPUT_DIR" ] 
then OUTPUT_DIR=$PWD
fi

# Self update
pushd .. >& /dev/null
svn -q update
popd >& /dev/null

#########################
# PART ONE: TWELF BUILD #
#########################

# Run build script and make dmg
./build.sh $OUTPUT_DIR keep >& $OUTPUT_DIR/new-build-output-1
cp /opt/local/lib/libgmp.a twelf/bin
make -C osx >& $OUTPUT_DIR/new-build-output-2
cat $OUTPUT_DIR/new-build-output-1 $OUTPUT_DIR/new-build-output-2 > $OUTPUT_DIR/new-build-output
rm -f $OUTPUT_DIR/new-build-output-1
rm -f $OUTPUT_DIR/new-build-output-2

# Attach new output to old output
pushd $OUTPUT_DIR >& /dev/null
touch build-output
mv build-output old-build-output
date | cat - new-build-output old-build-output > build-output

# Upload to remote directory
scp $OUTPUT_DIR/twelf-src.tar.gz $REMOTE_DIR/twelf-src.tar.gz
scp osx/Twelf.dmg $REMOTE_DIR/twelf-osx.dmg
scp $OUTPUT_DIR/new-build-output $REMOTE_DIR/osx-build-output

# Clean up
make -C osx clean >& /dev/null
rm -Rf twelf
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
pushd $OUTPUT_DIR >& /dev/null
touch regression-output
mv regression-output old-regression-output
date | cat - new-regression-output old-regression-output > regression-output

scp $OUTPUT_DIR/new-regression-output $REMOTE_DIR/regression-output

# Clean up
rm -f new-regression-output
rm -f old-regression-output
popd >& /dev/null


