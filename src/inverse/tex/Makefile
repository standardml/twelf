
NW_DIR = ../NW_TEX

default : main.dvi

NOWEB_FILES = clf spinelf context signat translate

vpath %.tex $(NW_DIR)
vpath %.nw ..

%.tex : %.nw
	noweave -delay $(WEAVE_FILTER) $< > $(NW_DIR)/$@


main.dvi : twelf_grammar.tex using.tex $(addsuffix .tex,$(NOWEB_FILES)) 


clean :
	-rm -rf $(JUNK_FILES)
