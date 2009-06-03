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
TIME="/usr/bin/time -f%e\treal\n%U\tuser"

echo "=== Compiling regression test package in MLton ==="
$TIME $MLTON -default-ann "nonexhaustiveMatch ignore" mlton-regression.cm

echo ""
echo "=== Running regression test in MLton ==="
$TIME ./mlton-regression regression.txt

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
  echo "=== Running misc. public code ==="
  $TIME ./mlton-regression regression-public.txt

  echo "==== Completed! ==="
fi

rm -f ./mlton-regression

 
