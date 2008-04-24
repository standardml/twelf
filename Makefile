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
mlton = mlton

twelfdir = `pwd`
twelfserver = twelf-server
version = TWELFVERSION

# ---------------------------------------------------------------
# You should not need to edit beyond this point
# ---------------------------------------------------------------

default: ;
	@echo "Options for building Twelf $(version):"
	@echo "   make smlnj   Make Twelf with SML/NJ version >=110.20"
#	@echo "   make old-nj  Make Twelf with SML/NJ version 110.0.3 or 110.0.7"
	@echo "   make mlton   Make Twelf with MLton"
	@echo ""
	@echo "To load Twelf in SML/NJ, use the \"sources.cm\" file in this directory."
	@echo ""

twelf-server-mlton: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"
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


twelf-server-smlnj: ;
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"	 
	$(smlnj) < build/twelf-server-smlnj.sml ;
	bin/.mkexec "$(smlnj)" "$(twelfdir)" twelf-server "$(twelfserver)" ;


twelf-emacs: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Emacs instructions"
	@echo "*************************************************"	 
	@echo "Add"
	@echo ""
	@echo "(setq twelf-root \"$(twelfdir)/\")"
	@echo "(load (concat twelf-root \"emacs/twelf-init.el\"))"
	@echo ""
	@echo "to your .emacs file"
	@echo "*************************************************"	

polyml : ;
	@echo "This makefile not yet working with PolyML."

smlnj : twelf-emacs twelf-server-smlnj

oldnj : ; # twelf-emacs twelf-server-smlnj-old
	@echo "This makefile not yet working with old versions of SML/NJ."

mlton : twelf-emacs twelf-server-mlton	

