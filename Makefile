# Twelf
# Copyright (C) 1997, 1998, Frank Pfenning and Carsten Schuermann

# ---------------------------------------------------------------
# Please edit the following lines
# ---------------------------------------------------------------

# What is SML/NJ called?
sml = sml-cm

# Twelf root directory
twelfdir = $(PWD)

# ---------------------------------------------------------------
# Do not edit the following lines
# ---------------------------------------------------------------

version = "1.2"

default : twelf-server twelf-emacs

all : twelf-server twelf-sml twelf-emacs

twelf-server: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"	 
	$(sml) < twelf-server.sml ;
	sed -e "s#%TWELFDIR#$(twelfdir)#g" \
	    -e "s#%SML#$(sml)#g" bin/.twelf-server \
	> bin/twelf-server ;
	chmod a+x bin/twelf-server ;

twelf-sml: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): SML"
	@echo "*************************************************"	 
	$(sml) < twelf-sml.sml ;
	sed -e "s#%TWELFDIR#$(twelfdir)#g" \
	    -e "s#%SML#$(sml)#g" bin/.twelf-sml \
	> bin/twelf-sml ;
	chmod a+x bin/twelf-sml ;

twelf-emacs: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Emacs"
	@echo "*************************************************"	 
	sed -e "s#%TWELFDIR#$(twelfdir)#g" emacs/.twelf-init.el \
	> emacs/twelf-init.el ;
	@echo "*************************************************"
	@echo "Add"
	@echo ""
	@echo "(load \"$(twelfdir)/emacs/twelf-init.el\")"
	@echo ""
	@echo "to your .emacs file"
	@echo "*************************************************"	


clean: ;
	rm -rf $(twelfdir)/src/*/CM ;
