
default : check

IMOGEN_HOME = ../../..

include $(IMOGEN_HOME)/Makefile.global

check : sources.mlb
	$(MLTON) -stop tc $<
