# Twelf
# Copyright (C) 1997-2000, Frank Pfenning and Carsten Schuermann

# Makefile for Twelf with Poly/ML
# Tested with Poly/ML 4.1.3 under Linux
#
# Invoke in Twelf root directory with
#
# make -f polyml/Makefile
#
# ---------------------------------------------------------------
# Please edit the following lines
# ---------------------------------------------------------------

# What is polyml called?
sml = poly

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

default : twelf-sml twelf-server twelf-emacs

all : twelf-sml twelf-server twelf-emacs

twelf-server: twelf-sml; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"	 
	$(sml) -r $(twelfdir)/bin/.dbase/twelf-sml < polyml/twelf-server-dbase.sml ;
	$(sml) $(twelfdir)/bin/.dbase/twelf-server < polyml/twelf-server.sml ;
	polyml/.mkexec "$(sml)" "$(twelfdir)" twelf-server "$(twelfserver)";

twelf-sml: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): SML"
	@echo "*************************************************"	 
	$(sml) < polyml/twelf-sml-dbase.sml ;
	$(sml) $(twelfdir)/bin/.dbase/twelf-sml < polyml/twelf-sml.sml ;
	polyml/.mkexec "$(sml)" "$(twelfdir)" twelf-sml "$(twelfsml)";

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
	@echo "No temporary files with Poly/ML"
