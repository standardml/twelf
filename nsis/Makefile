# Twelf
# Copyright (C) 1997-2000, Frank Pfenning and Carsten Schuermann

# ---------------------------------------------------------------
# Please edit the following lines
# ---------------------------------------------------------------

# What is SML/NJ called?
sml = sml-cm

# ---------------------------------------------------------------
# Do not edit the following lines
# ---------------------------------------------------------------

version = "1.3"

default : twelf-server

all : twelf-server twelf-sml

twelf-server: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): Server"
	@echo "*************************************************"	 
	$(sml) < twelf-server.sml ;

twelf-sml: ; 
	@echo "*************************************************"
	@echo "Twelf $(version): SML"
	@echo "*************************************************"	 
	$(sml) < twelf-sml.sml ;

clean: ;
	rm -rf src/*/CM ;
