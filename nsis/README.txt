Twelf
Copyright (C) 1997-2000, Frank Pfenning and Carsten Schuermann

Authors: Frank Pfenning
	 Carsten Schuermann
With contributions by:
	 Iliano Cervesato
	 Jeff Polakow
	 Roberto Virga

Twelf is an implementation of

 - the LF logical framework, including type reconstruction
 - the Elf constraint logic programming language
 - a meta-theorem prover for LF (very preliminary)
 - a set of expansion modules to deal natively with numbers and strings
 - an Emacs interface

This README file applies to version Twelf 1.3 alpha.
For current information regarding Twelf, see the Twelf home page at

  http://www.cs.cmu.edu/~twelf

Twelf can be compiled and installed under Unix, either as a separate
"Twelf Server" intended primarily as an inferior process to Emacs, or as
a structure Twelf embedded in Standard ML.
There is also self-extracting EXE file for Windows 9x/NT/ME/2000.

Files
=====

 README            --- this file
 Makefile          --- enables make
 load.sml          --- enables  use "load.sml"; (* especially for MLWorks *)
 twelf-server.sml  --- used to build Twelf Server
 twelf-sml         --- used to build Twelf SML
 bin/              --- utility scripts and heap location
 doc/              --- Twelf user's guide in various formats
 emacs/            --- Emacs interface for Twelf
 examples/         --- various case studies
 examples-clp/     --- examples of use of the numbers and strings extensions
 server.cm         --- enables make of Twelf server
 sources.cm        --- enables make of Twelf-SML
 src/              --- the SML sources for Twelf
 tex/              --- TeX macros and style files

Installation Instructions
=========================

These instructions apply to Unix or Windows 9x/ME/NT/2000 when compiling the
sources directly.  For Windows 9x/ME/NT/2000 there is also a self-extracting
EXE file with a much simpler installation procedure.

Installation requires Standard ML, Revision of 1997.
The Twelf Server requires SML of New Jersey.

If it is not installed already, please check

 SML of New Jersey [free]
    http://cm.bell-labs.com/cm/cs/what/smlnj/index.html
    (version 110 or higher)

 MLWorks [commercial]
    http://www.harlequin.com/products/ads/ml/ml.html


Platforms
=========

Twelf can be installed on different platforms, such as
Unix or Windows 9x/ME/NT/2000.  Note that these instructions 
are for SML of New Jersey, version 110 or higher.

Twelf can be installed as 

  Twelf-Server   (a stand-alone version to be used primarily within Emacs)

and

  Twelf-SML      (a version embedded into SML)


Instead of compiling Twelf for the Windows 9x/ME/NT/2000 family of
operating systems, we recommend instead to use the precompiled version
which is available from the Twelf homepage at

  http://www.cs.cmu.edu/~twelf/dist/twelf-1-3.exe


Unix Installation
=================


  Summary
  -------

      % gunzip twelf-1-3.tar.gz
      % tar -xf twelf-1-3.tar
      % cd twelf

    You may need to edit the file Makefile to give the proper location
    for sml-cm.  These instructions are for SML of New Jersey, version
    110 or higher.

      % make
      % bin/twelf-server
      Twelf 1.3, Oct 15 2000
      %% OK %%

    You can now load the examples from the User's Guide and pose an
    example query as shown below.  The prompt from the Twelf top-level
    is `?-'.  To drop from the Twelf top-level to the ML top-level, type
    C-c (CTRL c).  To exit the Twelf server you may issue the quit
    command or type C-d (CTRL d).

      Config.read examples/guide/sources.cfg
      Config.load
      top
      ?- of (lam [x] x) T.
      Solving...
      T = arrow T1 T1.
      More? y
      No more solutions
      ?- C-c
      interrupt
      %% OK %%
      quit
      %


  Detailed Instructions
  ---------------------  

  Step 0: Select directory/Unpack Twelf distribution

    First select a directory where you want Twelf to reside. Note that
    the Twelf installation cannot be moved after it has been compiled
    with make, since absolute pathnames are built into the executable
    scripts.  If you install Twelf as root, a suitable directory would
    be

		/usr/local/lib

    but any other directory will work, too, as long it does not contain
    any whitespace characters. Since the distribution
    is unpacked into a subdirectory called `twelf' you should make
    sure such a directory does not already exist.

    Unpack the distribution in this directory: 	
    ( % is assumed to be the shell prompt.) 

	  % gunzip twelf-1-3.tar.gz
	  % tar -xf twelf-1-3.tar
	  % cd twelf


  Step 1: Compile Twelf

    You may need to edit the file Makefile to give the proper location
    for sml-cm (SML of New Jersey version 110 or higher, with the
    compilation manager pre-loaded).

    Twelf-Server: [Default]

	If you would like to build the Twelf server, whose primary use
	is as an inferior process to Emacs, call

	  % make

        This builds the Twelf server for your current architecture and
        makes it accessible as bin/twelf-server.  Under Linux, the heap
        image is about 1.6MB.  It also installs the Twelf Emacs
        interface, but you must add the two lines

	  (setq twelf-root "<directory>")
	  (load (concat twelf-root "emacs/twelf-init.el"))

	to your .emacs file, where <directory> is the root directory
	(slash-terminated) into which you installed Twelf.

        To test whether the binary has been created properly, try

	  % bin/twelf-server

        in the Twelf root directory.  Use 'quit' to exit the server.

    Twelf-SML: 
	
	If you would like to use Twelf as a structure in SML, you 
	can then call

	  % make twelf-sml

	in the root directory into which you installed Twelf.  This
	creates bin/twelf-sml which is a rather large heap image (e.g.,
	11MB under Linux) since it include the SML/NJ compiler.

    Full installation:

	If you would like to install the Twelf-Server and Twelf-SML,
	you can then call

	  % make all

        This builds both the Twelf-Server and Twelf-SML for your current
        architecture and makes them accessible as bin/twelf-server and
        bin/twelf-sml, respectively.  It also installs the Twelf Emacs
        interface, but, as above, you must add the two lines

	  (setq twelf-root "<directory>")
	  (load (concat twelf-root "emacs/twelf-init.el"))

	into your .emacs file, where <directory> is the root directory
	(terminated by a "/") into which you installed Twelf.

  Step 2:  Removing temporary files

	The installation of the Twelf-Server and Twelf-SML creates
	various temporary files, which may be removed after a
	successful installation with

	  % make clean


  Troubleshooting:
	
	Early versions of SML 110 of New Jersey do not support the
	switch for SML garbage collection messages from within SML
	triggered by the command

		SMLofNJ.Internals.GC.messages false;

	This feature is used in twelf-server.sml and twelf-sml.sml,
	the two files which compile the Twelf system. If SML complains
	about these lines either install a newer version of SML 110 of 
	New Jersey, or comment out this line.


Windows 9x/ME/NT/2000 Installation
==================================

  Standard Installation
  ---------------------
    For the Windows 9x/ME/NT/2000 family of operating systems, we
    recommend the precompiled version of the Twelf server which is
    available from the Twelf homepage at

          http://www.cs.cmu.edu/~twelf/dist/twelf-1-3.exe

    which is a self-installing EXE file.

    Twelf has been tested to work with NTEmacs which is freely 
    available from

       ftp://ftp.cs.washington.edu/pub/ntemacs

    You can also use the Win32 port of XEmacs, available from

       ftp://ftp.xemacs.org/xemacs/binary-kits/win32/ 

    Step 0: Extract the Twelf distribution

      Unpack and install the distribution by running the executable.
      In particular, you will be asked to select a directory where you
      want Twelf to reside.

    Step 1: Edit your _emacs file

      In order to use Twelf with the Emacs (recommended) interface, you
      will need to edit your _emacs file (see the NTEmacs and/or consult
      your system administrator if you do not know the location of this
      file).
      If, for example, you installed Twelf in

          C:\Program Files\Twelf

      you will need to add the following two lines:

	  (setq twelf-root "C:/Program Files/Twelf/")
	  (load (concat twelf-root "emacs/twelf-init.el"))

      to your _emacs file. Note that NTEmacs requires the use of the
      slash ("/") instead of Windows traditional backslash ("\") symbol
      as path separator.

    NOTE. It is important that you do not move the Twelf distribution
    files from the location where you originally installed them. The
    installation procedure creates some scripts that depend on the
    installation path. To move Twelf to a different location, uninstall
    it and install it again to the new path.

  Full Installation
  -----------------

    If, during the installation, you chose to install the source
    distribution, you will also be able to compile Twelf yourself.
    In order to do so, however, you will additionally need:
    
      - the Cygwin tools, available from:
	http://www.cygwin.com/
        (version 1.1 or higher)

      - Standard ML of New Jersey, available from:
        http://cm.bell-labs.com/cm/cs/what/smlnj/index.html
        (version 110 or higher)

    Be sure sml-cm.bat is in your Path, or otherwise edit the Makefile
    to specify its location.

      Twelf-Server: [Default]
	
	If you would like to build the Twelf server, whose primary use
	is as an inferior process to Emacs, type

	  bash-2.03$ make

        ("bash-2.03$" is the Cygwin command-line prompt).
        This builds the Twelf server for your current architecture 
	and makes it accessible as  bin\twelf-server.bat.

        To test whether the binary has been created properly, try

	  bash-2.03$ bin\twelf-server

        in the Twelf root directory.

    Twelf-SML: 
	
	If you would like to use Twelf as a structure in SML, you 
	can then type

	  bash-2.03$ make twelf-sml

	in the root directory into which you installed Twelf.
	This  creates  bin\twelf-sml.bat. 

    Full installation:

	If you would like to install the Twelf-Server and Twelf-SML,
	you can then call

	  bash-2.03$ make all

        This builds both the Twelf-Server and Twelf-SML for your current
        architecture and makes them accessible as bin\twelf-server.bat
        and bin\twelf-sml.bat, respectively.

    Removing temporary files:
	
	The installation of the Twelf-Server and Twelf-SML creates
	various temporary files, which may be removed after a 
	successful installation with

	  bash-2.03$ make clean

