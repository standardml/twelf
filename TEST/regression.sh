#!/bin/bash
# TWELF REGRESSION TEST
# Author: Robert J. Simmons
# 
# TEST/regression.sh [ full ]
# Tests the regression suite, provides timing information. 
# Should stay largely silent if there are no problems.
# If no second argument is given, just does the superficial regression suite;
# if any second argument is given, the script also runs several plparty.org 
# specific extra regression checks.

MLTON="mlton"
SML="sml"
SML_FLAGS="-Ccm.verbose=false -Ccompiler-mc.warn-non-exhaustive-match=false sources.cm -Ccompiler-mc.warn-non-exhaustive-bind=false -Ccontrol.poly-eq-warn=false"
POSTFIX=$( date +%y%m%d )
if [ $TERM_PROGRAM -eq "Apple_Terminal" ] 
then ## Better OS X test? Really maybe don't care as much, run make check
  TIME="/usr/bin/time"
else
  TIME="/usr/bin/time -f%e\treal\n%U\tuser"
fi

echo "=== Compiling regression test package in MLton ==="
make -C .. twelf-regression

echo ""
echo "=== Running regression test in MLton ==="
$TIME ../bin/twelf-regression regression.txt

echo ""
echo "=== Running Karl Crary's 'papers' page ==="
$TIME ../bin/twelf-regression regression-crary.txt

echo ""
echo "=== Running misc. public code ==="
$TIME ../bin/twelf-regression regression-public.txt

echo ""
echo "=== Running Twelf Wiki literate examples ==="
$TIME ../bin/twelf-regression regression-wiki.txt


ARG_ONE=$1
if [ -z "$ARG_ONE" ] 
then
  echo "==== Completed! ==="
else
  echo ""
  echo "=== Running TALT ==="
  $TIME ./mlton-regression regression-talt.txt

  echo ""
  echo "=== Running TS-LF (Definition of Standard ML) ==="
  $TIME ./mlton-regression regression-tslf.txt

  echo ""
  echo "=== Running Princeton Foundational PCC ==="
  $TIME ./mlton-regression regression-fpcc.txt

  echo "==== Completed! ==="
fi

rm -f ./mlton-regression

 
