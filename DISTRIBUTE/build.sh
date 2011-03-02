#!/bin/bash
# TWELF LINUX BUILD FILE
# Author: Robert J. Simmons
# 
# ./build.sh [destination_directory] [keep_files]
# If no destination_directory is given, then files are places in the 
# current directory
# If any second argument is given, then the "build/twelf" directory is 
# left behind at the end of execution

# Otherwise than an exit message, this script is intended to be silent
# unless something goes wrong.


###################
# PART ONE: SETUP #
###################

MLTON="mlton"
SML="smlnj"

# Parse destination directory
DESTINATION=$1
if [ -z "$DESTINATION" ] 
then DESTINATION=$PWD
fi

#########################
# PART TWO: EXPORT COPY #
#########################

# Get files
rm -Rf twelf
svn -q export https://cvs.concert.cs.cmu.edu/twelf/trunk twelf
rm -Rf twelf/HISTORY
rm -Rf twelf/DISTRIBUTE
rm -Rf twelf/TEST
rm -Rf twelf/tools
rm -Rf twelf/TODO
rm -Rf twelf/exercises

###################################
# PART THREE: CREATE OUTPUT FILES #
###################################

# Build source tarball while copy is still clean
tar -czf "$DESTINATION/twelf-src.tar.gz" twelf

# Build binary
../bin/buildid >twelf/src/frontend/buildid.sml
make -s -C twelf twelf-server-mlton

# Delete files that not needed for a binary release
rm -Rf twelf/src
rm -Rf twelf/Makefile
rm -Rf twelf/build
rm -Rf twelf/*.sml
rm -Rf twelf/*.cm

# Build binary tarball
tar -czf "$DESTINATION/twelf-compiled.tar.gz" twelf

# Possibly delete files
if [ -z "$2" ] 
then
rm -Rf twelf
fi

echo "Build script complete; exiting"



