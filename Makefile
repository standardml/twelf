# Twelf
# Copyright (C) 1997-2000, Frank Pfenning and Carsten Schuermann

# ---------------------------------------------------------------
# Please edit the following lines
# ---------------------------------------------------------------

# What is SML/NJ called?
sml = $(shell which sml-cm)

# Twelf root directory
twelfdir = $(shell pwd)

# ---------------------------------------------------------------
# Do not edit the following lines
# ---------------------------------------------------------------

version = "1.3"

default : twelf-server twelf-emacs

all : twelf-server twelf-sml twelf-emacs

twelf-server: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"	 
	$(sml) < twelf-server.sml ;
	bin/.mkexec "$(sml)" "$(twelfdir)" twelf-server ;

twelf-sml: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): SML"
	@echo "*************************************************"	 
	$(sml) < twelf-sml.sml ;
	bin/.mkexec "$(sml)" "$(twelfdir)" twelf-sml ;

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
