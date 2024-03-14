---
title: Download Twelf
prev: false
next: false
---

The current version of Twelf can be [downloaded from
GitHub](https://github.com/standardml/twelf/releases/latest). We strongly
suggest using the source distribution or checking out the latest version, as
the binary distributions are from, like, 2011.

## Installing Twelf from source

Twelf can be compiled with two of the most common compilers for Standard ML. In
addition to the compiler, you will need the standard unix-style Make tools.
These come with basically any Linux distribution.

### Installing with SML/NJ

You will need to have the Standard ML of New Jersey software on your computer.
This can be obtained from the [SML/NJ website](http://www.smlnj.org/).

Once you have the prerequisites, Twelf can be built by running

```bash
cd twelf
make smlnj
```

### Installing with MLton

You will need to have the MLton compiler on your computer. This can be obtained
from the [MLton website](http://mlton.org/).

Once you have the prerequisites, Twelf can be built by running

```bash
cd twelf
make mlton
```

## Using Twelf with Emacs

The preferred way to interact with Twelf is through its Emacs mode. The `make`
command that you use to build Twelf will tell you to add two lines somewhere
in your `~/.emacs` file. (If you don't have a `.emacs` file in your home
directory, you can create one and add those two lines).

See [Using Twelf with Emacs](/wiki/twelf-with-emacs/) for the next steps.

## Using Twelf without Emacs

It's possible to use Twelf without Emacs, and many of the most prolific Twelf
authors have historically eschewed the Emacs mode. See [Using Twelf without
Emacs](/wiki/twelf-without-emacs/) for the next steps.

## Older versions

See the [release history](/release-history/).