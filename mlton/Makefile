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
	mltonversion=`$(sml) 2>&1 | awk 'NR==1 { print 0+$$2 }'`;	\
	if   [ $$mltonversion -ge 20040227 ]; then			\
		cmfileid="";						\
	elif [ $$mltonversion -ge 20030716 ]; then			\
		cmfileid="-20030716";					\
	else								\
		cmfileid="-97";						\
	fi;								\
	$(sml) mlton/twelf-server$${cmfileid}.cm ;			\
	mv mlton/twelf-server$${cmfileid} bin/$(twelfserver)

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


mlton-cm-files: twelf-server-cm twelf-server-20030716-cm twelf-server-97-cm ;

twelf-server-cm: ;
	{							\
	echo "(* MLton version *)" ;				\
	echo "(* For use with MLton >= 20040227 *)" ;		\
	echo "Group is" ;					\
	cmcat -DMLton_20040227 -DMLton_20030716 ../server.cm ;	\
	echo "twelf-server.sml" ;				\
	}							\
	> twelf-server.cm

twelf-server-20030716-cm: ;
	{						\
	echo "(* MLton version *)" ;			\
	echo "(* For use with MLton >= 20030716 *)" ;	\
	echo "Group is" ;				\
	cmcat -DMLton_20030716 ../server.cm ;		\
	echo "twelf-server.sml" ;			\
	}						\
	> twelf-server-20030716.cm

twelf-server-97-cm: ;
	{						\
	echo "(* MLton version *)" ;			\
	echo "(* For use with MLton < 20030716 *)" ;	\
	echo "Group is" ;				\
	cmcat ../server.cm ;				\
	echo "twelf-server.sml" ;			\
	}						\
	> twelf-server-97.cm
