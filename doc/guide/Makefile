# Twelf
# Copyright (C) 1997, 1998, Frank Pfenning and Carsten Schuermann

# ---------------------------------------------------------------
# Please edit the following lines
# ---------------------------------------------------------------

# Various program locations
tex = tex
dvips = dvips
texi2html = /afs/cs/project/twelf/misc/texi2html/texi2html
makeinfo = makeinfo
distill = distill

# ---------------------------------------------------------------
# Do not edit the following lines
# ---------------------------------------------------------------

all : twelf.info twelf.dvi twelf.ps twelf_toc.html twelf.pdf

twelf.info : twelf.texi;
	@echo "Creating twelf.info"
	$(makeinfo) twelf.texi;

twelf.dvi : twelf.texi;
	@echo "Creating twelf.dvi"
	$(tex) twelf.texi;

twelf.ps : twelf.dvi;
	@echo "Creating twelf.ps"
	$(dvips) -o twelf.ps twelf;

twelf_toc.html : twelf.texi;
	@echo "Creating twelf_*.html"
	$(texi2html) -menu -number -split_chapter twelf.texi;
	$(texi2html) -check *.html;

twelf.pdf : twelf.dvi;
	@echo "Trying to create twelf.pdf"
	@case "`uname`" in Linux) \
	echo "distill not available under Linux" ; exit 1 ; \
	;; esac;
	$(dvips) -P embed -f twelf.dvi | $(distill) > twelf.pdf;

install : ;
	@echo "Copying info file"
	cp -p twelf.info* ../info/
	@echo "Copying dvi file"
	cp -p twelf.dvi ../dvi/
	@echo "Copying ps file"
	cp -p twelf.ps ../ps/
	@echo "Copying ps.gz file"
	gzip -c twelf.ps > twelf.ps.gz
	@echo "Copying pdf file"
	@echo "Is the PDF file really up-to-date?"
	cp -p twelf.pdf ../pdf/
	@echo "Copying html files"
	cp -p twelf_*.html ../html/
	@echo "Consider install-www for release of a new version"

install-www : ;
	@echo "Copying ps file"
	cp -p twelf.ps /afs/cs/project/twelf/www/guide/
	@echo "Copying ps.gz file"
	gzip -c twelf.ps > twelf.ps.gz
	cp -p twelf.ps.gz /afs/cs/project/twelf/www/guide/
	@echo "Copying pdf file"
	@echo "Is the PDF file really up-to-date?"
	cp -p twelf.pdf /afs/cs/project/twelf/www/guide/
	@echo "Copying html files"
	cp -p twelf_*.html /afs/cs/project/twelf/www/guide/
	@echo "Please edit ~twelf/www/index.html as necessary"

clean : ;
	rm -f twelf.dvi;
	rm -f twelf.ps;
	rm -f twelf.ps.gz;
	rm -f twelf.pdf;
	rm -f twelf_*.html;
	rm -f twelf.info*;
	rm -f twelf.{aux,log};
	rm -f twelf.{cp,cps,fn,fns,ky,pg,toc,tp,vr};