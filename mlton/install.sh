#!/bin/sh
#
# Trivial installation script for Twelf with MLton
# Tested with MLton 20020923 under Linux
#
# Invoke in Twelf root directory with
#
# mlton/install.sh

# Change next four lines as needed
sml=mlton
twelfdir=`pwd`
twelfserver=twelf-server

version="1.4"

echo "*************************************************"
echo "Twelf $version: Server"
echo "*************************************************"
$sml mlton/twelf-server.cm
mv twelf-server bin/$twelfserver

echo "*************************************************"
echo "Twelf $version: Emacs"
echo "*************************************************"	 
echo "Add"
echo ""
echo "(setq twelf-root \"$twelfdir/\")"
echo "(load (concat twelf-root \"emacs/twelf-init.el\"))"
echo ""
echo "to your .emacs file"
echo "*************************************************"	
