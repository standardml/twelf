Twelf
=====
[![run tests](https://github.com/standardml/twelf/actions/workflows/run-tests.yml/badge.svg?branch=main)](https://github.com/standardml/twelf/actions/workflows/run-tests.yml)

Copyright (C) 1997-2011, Frank Pfenning and Carsten Schuermann

Authors: 
 - Frank Pfenning
 - Carsten Schuermann

With contributions by:
 - Brigitte Pientka
 - Roberto Virga
 - Kevin Watkins
 - Jason Reed

Twelf is an implementation of

 - the LF logical framework, including type reconstruction
 - the Elf constraint logic programming language
 - a meta-theorem prover for LF (very preliminary)
 - a set of expansion modules to deal natively with numbers and strings
 - an Emacs interface

Installing
==========

For complete installation instructions, see http://twelf.org/

Twelf can be compiled and installed under Unix, either as a separate
"Twelf Server" intended primarily as an inferior process to Emacs, or as
a structure Twelf embedded in Standard ML.

To build with SML of New Jersey type "make smlnj." To build with MLton type
"make mlton." If you are building Twelf through SML of New Jersey, you may need
to run "make buildid" first.

Files
=====

    README.md         --- this file
    Makefile          --- enables make
    server.cm         --- used to build Twelf Server
    sources.cm        --- used to build Twelf SML
    bin/              --- utility scripts, heaps, binaries
    build/            --- build files (type "make" to see options)
    doc/              --- (Outdated) Twelf user's guide
    emacs/            --- Emacs interface for Twelf
    examples/         --- various case studies
    examples-clp/     --- examples of use of the numbers and strings extensions
    src/              --- the SML sources for Twelf
    tex/              --- TeX macros and style files
    vim/              --- Vim interface for Twelf
