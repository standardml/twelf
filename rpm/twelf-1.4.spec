Summary: Twelf 1.4
Name: twelf
Version: 1.4
Release: 0
Copyright: Frank Pfenning and Carsten Schuermann
Group: Development/Languages
Source: http://www.cs.cmu.edu/~twelf/dist/twelf-1-4.tar.gz
URL: http://www.cs.cmu.edu/~twelf/
Icon: logo.gif

%description
Twelf is an implementation of

 - the LF logical framework, including type reconstruction
 - the Elf constraint logic programming language
 - meta-theorem verifier for LF
 - a meta-theorem prover for LF (preliminary)
 - an Emacs interface

It also includes a complete User's Guide and example suite; a tutorial
is available from Frank Pfenning <fp@cs.cmu.edu>.  Twelf is written in
Standard ML and uses an inference engine based on explicit
substitutions.  Twelf has been developed at Carnegie Mellon University,
Yale University, and Princeton University and runs under SML/NJ and
MLWorks on various Unix platforms, Windows 95/98/NT and Mac OS X

%prep
%setup -n twelf

%build
make -f mlton/Makefile

%install
rm -rf /usr/share/twelf
mkdir -p /usr/share/twelf
cp -rf bin /usr/share/twelf
cp -rf emacs /usr/share/twelf
cp -rf examples /usr/share/twelf
cp -rf examples-clp /usr/share/twelf
cp -rf tex /usr/share/twelf
cp -rf doc /usr/share/twelf
ln -sf /usr/share/twelf/bin/twelf-server /usr/bin/twelf-server

%clean
rm -rf $RPM_BUILD_ROOT

%postun
rm -rf /usr/share/twelf
rm -f /usr/bin/twelf-server

%changelog
* Fri Dec 27 2002 Frank Pfenning <fp@cs.cmu.edu>
- RPM for version 1.4 (alpha)
- This version built from MLton, since it has stand-alone binaries
* Wed Oct 18 2000 Roberto Virga <rvirga@cs.princeton.edu> 
- first RPM for release 1.3 (alpha)

