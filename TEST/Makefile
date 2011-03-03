# Makefile for running regression test
# Rob Simmons

# Expects to be called from root directory makefile, with test binary already
# freshly built from current source.

test = ../bin/twelf-regression

.PHONY: check
check: 
	$(test) regression.txt
	$(test) regression-public.txt
	$(test) regression-wiki.txt
	$(test) regression-crary.txt