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

# Exit on error
set -e

MLTON="mlton"
SML="sml"
SML_FLAGS="-Ccm.verbose=false -Ccompiler-mc.warn-non-exhaustive-match=false sources.cm -Ccompiler-mc.warn-non-exhaustive-bind=false -Ccontrol.poly-eq-warn=false"
POSTFIX=$( date +%y%m%d )
if [[ $TERM_PROGRAM == "Apple_Terminal" ]]
then ## Better OS X test? Really maybe don't care as much, run make check
  TIME="/usr/bin/time"
else
  TIME="/usr/bin/time -f%e\treal\n%U\tuser"
fi

startgroup() {
    if [ -z "$GITHUB_WORKFLOW" ]; then
        echo ""
        echo "=== $1 ==="
    else
        echo "::group::$1"
    fi
}

endgroup() {
    if [ -z "$GITHUB_WORKFLOW" ]; then
        :
    else
        echo "::endgroup::"
    fi
}

startgroup "Compiling regression test package in MLton"
make -C .. twelf-regression
endgroup

startgroup "Running regression test in MLton"
$TIME ../bin/twelf-regression regression.txt
endgroup

startgroup "Running Karl Crary's 'papers' page"
$TIME ../bin/twelf-regression regression-crary.txt
endgroup

startgroup "Running misc. public code"
$TIME ../bin/twelf-regression regression-public.txt
endgroup

startgroup "Running Twelf Wiki literate examples"
node regression-wiki.mjs
$TIME ../bin/twelf-regression regression-wiki.txt
endgroup

ARG_ONE=$1
if [ -z "$ARG_ONE" ]
then
  echo "=== Completed! ==="
else
  startgroup "Extra Tests"

  startgroup "Running TALT"
  $TIME ../bin/twelf-regression regression-talt.txt
  endgroup

  startgroup "Running TS-LF (Definition of Standard ML)"
  $TIME ../bin/twelf-regression regression-tslf.txt
  endgroup

  startgroup "Running Princeton Foundational PCC"
  $TIME ../bin/twelf-regression regression-fpcc.txt
  endgroup

  endgroup # Extra Tests
  echo "=== Completed! ==="
fi
