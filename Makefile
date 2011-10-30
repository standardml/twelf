# Makefile for Twelf Server
# Copyright (C) 1997-2006, Frank Pfenning, Carsten Schuermann, and others
# Available under a BSD license, see LICENSE

# ---------------------------------------------------------------
# The following lines attempt to set default names of compilers
# and locations; if these defaults are wrong, edit the following
# lines.
# ---------------------------------------------------------------

polyml = poly
smlnj = sml
oldnj = sml
mlton = mlton -default-ann 'nonexhaustiveMatch ignore'
make = make

twelfdir = `pwd`
twelfserver = twelf-server

# ---------------------------------------------------------------
# You should not need to edit beyond this point
# ---------------------------------------------------------------

.PHONY: default
default: ;
	@echo "Options for building Twelf:"
	@echo "   make smlnj   Make Twelf with SML/NJ"
	@echo "   make mlton   Make Twelf with MLton"
	@echo ""
	@echo "To load Twelf in SML/NJ, use the \"sources.cm\" file in this directory."
	@echo ""

.PHONY: buildid
buildid:
	-rm -Rf src/frontend/buildid.sml
	bin/buildid >src/frontend/buildid.sml


.PHONY: twelf-server-announce
twelf-server-announce:
	@echo "*************************************************"
	@echo "Twelf Server"
	@echo "*************************************************"

.PHONY: twelf-server-mlton
twelf-server-mlton:
	mltonversion=`$(mlton) 2>&1 | awk 'NR==1 { print 0+$$2 }'`;	\
	if   [ $$mltonversion -ge 20041109 ]; then			\
		cmfileid="twelf-server-mlton.cm";			\
	elif [ $$mltonversion="MLTONVERSION" ]; then			\
		cmfileid="twelf-server-mlton.cm";			\
	else								\
		echo; echo "Error: MLton >= 20041109 required";	echo;	\
		exit 1;							\
	fi;								\
	$(mlton) -output bin/$(twelfserver) build/$${cmfileid}

.PHONY: twelf-server-smlnj
twelf-server-smlnj:
	$(smlnj) < build/twelf-server-smlnj.sml ;
	bin/.mkexec "$(smlnj)" "$(twelfdir)" twelf-server "$(twelfserver)" ;

.PHONY: twelf-emacs
twelf-emacs: ; 
	@echo "*************************************************"
	@echo "Twelf Emacs Integration"
	@echo "*************************************************"	 
	@echo "Add"
	@echo ""
	@echo "(setq twelf-root \"$(twelfdir)/\")"
	@echo "(load (concat twelf-root \"emacs/twelf-init.el\"))"
	@echo ""
	@echo "to your .emacs file"
	@echo "*************************************************"	

.PHONY: poylml smlnj oldnj mlton

polyml : ;
	@echo "This makefile not yet working with PolyML."

smlnj : twelf-server-announce buildid twelf-server-smlnj twelf-emacs

mlton : twelf-server-announce buildid twelf-server-mlton twelf-emacs 

.PHONY: twelf-regression check
twelf-regression: buildid
	$(mlton) -output bin/twelf-regression TEST/mlton-regression.cm

check : twelf-regression
	$(make) -C TEST check

smackage-install: 
	cp bin/twelf-server ../../../bin/twelf-server