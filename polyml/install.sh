#!/bin/sh
#
# Trivial installation script for Poly/ML
# Tested with Poly/ML 4.1.3 under Linux
#
# Invoke in Twelf root directory with
#
# polyml/install.sh

# Change next four lines as needed
sml=poly
twelfdir=`pwd`
twelfserver=twelf-server
twelfsml=twelf-sml

version="1.4"

echo "*************************************************"
echo "Twelf $version: SML"
echo "*************************************************"	 
$sml < polyml/twelf-sml-dbase.sml
$sml bin/.dbase/twelf-sml < polyml/twelf-sml.sml
polyml/.mkexec "$sml" "$twelfdir" twelf-sml "$twelfsml"

echo "*************************************************"
echo "Twelf $version: Server"
echo "*************************************************"	 
$sml -r bin/.dbase/twelf-sml < polyml/twelf-server-dbase.sml
$sml bin/.dbase/twelf-server < polyml/twelf-server.sml
polyml/.mkexec "$sml" "$twelfdir" twelf-server "$twelfserver"

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
