#!/bin/sh
#
# Trivial installation script for SML/NJ, versions >= 110.20
# This installs $twelf/bin/twelf-server
#
# Invoke in twelf root directory with
#
# smlnj/install.sh

# Change next three lines as needed
sml=`which sml`
twelfdir=`pwd`
twelfserver=twelf-server

version="1.4"

echo "*************************************************"
echo "Twelf $version: Server"
echo "*************************************************"	 
$sml < smlnj/twelf-server.sml ;
bin/.mkexec "$sml" "$twelfdir" twelf-server "$twelfserver" ;

echo "*************************************************"
echo "Twelf $version: Emacs"
echo "*************************************************"	 
echo "Add"
echo ""
echo "(setq twelf-root \"$(twelfdir)/\")"
echo "(load (concat twelf-root \"emacs/twelf-init.el\"))"
echo ""
echo "to your .emacs file"
echo "*************************************************"	
