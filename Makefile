# Twelf
# Copyright (C) 1997-2000, Frank Pfenning and Carsten Schuermann

# Makefile for Twelf with SML/NJ version 110.0.3 or 110.0.7
#
# Invoke in Twelf root directory with
#
# make
#
# ---------------------------------------------------------------
# Please edit the following lines
# ---------------------------------------------------------------

# What is SML/NJ called?
# We need the full pathname to create the executable
sml = `which sml`

# Twelf root directory
twelfdir = `pwd`

# Name of twelf-server program
twelfserver = twelf-server
# Name of twelf-sml program
twelfsml = twelf-sml

# ---------------------------------------------------------------
# Do not edit the following lines
# ---------------------------------------------------------------

version = "1.4"

default : twelf-server twelf-emacs

all : twelf-server twelf-sml twelf-emacs

twelf-server: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"	 
	$(sml) < twelf-server.sml ;
	bin/.mkexec "$(sml)" "$(twelfdir)" twelf-server "$(twelfserver)" ;

twelf-sml: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): SML"
	@echo "*************************************************"	 
	$(sml) < twelf-sml.sml ;
	bin/.mkexec "$(sml)" "$(twelfdir)" twelf-sml "$(twelfsml)" ;

twelf-emacs: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Emacs"
	@echo "*************************************************"	 
	@echo "Add"
	@echo ""
	@echo "(setq twelf-root \"$(twelfdir)/\")"
	@echo "(load (concat twelf-root \"emacs/twelf-init.el\"))"
	@echo ""
	@echo "to your .emacs file"
	@echo "*************************************************"	


clean: ;
	rm -rf $(twelfdir)/src/*/CM ;
