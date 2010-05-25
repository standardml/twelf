#!/bin/bash
# TWELF LINUX BUILD FILE
# Author: Robert J. Simmons
# 
# ./build.sh [destination_directory]
# If no destination_directory is given, then files are places in the 
# current directory

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

# Get version number
SVN_VERSION="$(awk '{ print $2 }' < subversion-version)"

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

sed "s/BUILT_FROM_SVN/Auto (Subversion r$SVN_VERSION)/g" twelf/src/frontend/twelf.fun > twelf/src/frontend/twelf-backup.fun
mv twelf/src/frontend/twelf-backup.fun twelf/src/frontend/twelf.fun

###################################
# PART THREE: CREATE OUTPUT FILES #
###################################

# Build source tarball while copy is still clean
tar -czf "$DESTINATION/twelf-src.tar.gz" twelf

$MLTON -default-ann "nonexhaustiveMatch ignore" \
    -output twelf/bin/twelf-server twelf/build/twelf-server-mlton.cm 

# Delete files that not needed for a binary release
rm -Rf twelf/src
rm -Rf twelf/Makefile
rm -Rf twelf/build
rm -Rf twelf/*.sml
rm -Rf twelf/*.cm

# Build binary Linux tarball
tar -czf "$DESTINATION/twelf-linux.tar.gz" twelf

rm -Rf twelf

echo "Build script complete; exiting"



