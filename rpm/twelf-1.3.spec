Summary: Twelf 1.3
Name: twelf
Version: 1.3
Release: 0
Copyright: Frank Pfenning and Carsten Schuermann
Group: Development/Languages
Source: http://www.cs.cmu.edu/~twelf/dist/twelf-1-3.tar.gz
URL: http://www.cs.cmu.edu/~twelf/
Requires: smlnj >= 110.0.6
Icon: logo.gif

%description
Twelf is an implementation of

 - the LF logical framework, including type reconstruction
 - the Elf constraint logic programming language
 - a meta-theorem prover for LF (very preliminary)
 - an Emacs interface

It also includes a complete User's Guide and example suite; a tutorial
is available from Frank Pfenning <fp@cs.cmu.edu>.  Twelf is written in
Standard ML and uses an inference engine based on explicit
substitutions.  Twelf has been developed at Carnegie Mellon University
and runs under SML/NJ and MLWorks on various Unix platforms and Windows
95/98/NT.

%prep
%setup -n twelf-1-3

%build
make

%install
rm -rf /usr/doc/twelf
mkdir -p /usr/doc/twelf
cp -f README /usr/doc/twelf
cp -rf doc/* /usr/doc/twelf
rm -rf /usr/share/twelf
mkdir -p /usr/share/twelf
cp -rf bin /usr/share/twelf
cp -rf emacs /usr/share/twelf
cp -rf examples /usr/share/twelf
cp -rf examples-clp /usr/share/twelf
cp -rf tex /usr/share/twelf
/usr/share/twelf/bin/.mkexec /usr/bin/sml /usr/share/twelf twelf-server
ln -sf /usr/share/twelf/bin/twelf-server /usr/bin/twelf-server

%clean
rm -rf $RPM_BUILD_ROOT

%postun
rm -rf /usr/doc/twelf
rm -rf /usr/share/twelf
rm -f /usr/bin/twelf-server

%changelog
* Wed Oct 18 2000 Roberto Virga <rvirga@cs.princeton.edu> 
- first RPM for release 1.3 (alpha)

