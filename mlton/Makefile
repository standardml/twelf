# Twelf
# Copyright (C) 1997-2000, Frank Pfenning and Carsten Schuermann

# Makefile for Twelf with MLton
# Tested with MLton 20030716 under Linux
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

# Cannot build twelf-sml or delphin under MLton, only twelf-server
twelfserver = twelf-server

# ---------------------------------------------------------------
# Do not edit the following lines
# ---------------------------------------------------------------

version = "1.5"
delphinversion = "0.1"

default : twelf-server twelf-emacs

all : twelf-server twelf-emacs

twelf-server: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"
	$(sml) -output bin/$(twelfserver) mlton/twelf-server.cm ;

twelf-sml: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Cannot build twelf-sml with MLton"
	@echo "*************************************************"

delphin: ; 
	@echo "*************************************************"
	@echo "Delphin $(delphinversion): Cannot build delphin with MLton"
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
