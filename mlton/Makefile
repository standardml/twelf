# Twelf
# Copyright (C) 1997-2000, Frank Pfenning and Carsten Schuermann

# Makefile for Twelf with MLton
# Tested with MLton 20020923 under Linux
# 
# Invoke in Twelf root directory with
#
# make -f mlton/Makefile
#
# ---------------------------------------------------------------
# Please edit the following lines
# ---------------------------------------------------------------

# What is MLton called?
sml = mlton

# Twelf root directory
twelfdir = `pwd`

# Cannot build twelf-sml under MLton, only twelf-server
twelfserver = twelf-server

# ---------------------------------------------------------------
# Do not edit the following lines
# ---------------------------------------------------------------

version = "1.4"

default : twelf-server twelf-emacs

all : twelf-server twelf-emacs

twelf-server: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"
	$(sml) mlton/twelf-server.cm ;
	mv mlton/twelf-server bin/$(twelfserver) ;

twelf-sml: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Cannot build twelf-sml with MLton"
	@echo "*************************************************"

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
	@echo "No temporary files with MLton"
