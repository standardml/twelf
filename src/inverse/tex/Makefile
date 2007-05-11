
NW_DIR = ../NW_TEX

NOWEB_FILES = spinelf context signat translate sequent

default : $(addsuffix .tex,$(NOWEB_FILES))

vpath %.tex $(NW_DIR)
vpath %.nw ..

%.tex : %.nw
	noweave -delay $(WEAVE_FILTER) $< > $(NW_DIR)/$@


main.dvi : twelf_grammar.tex using.tex $(addsuffix .tex,$(NOWEB_FILES)) 


clean :
	-rm -rf $(JUNK_FILES)
