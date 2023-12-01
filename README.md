Gencot - Verifying C Through Translation to Cogent
==================================================

Gencot is a tool for translating C code to Cogent.

State
-----

This is work in progress in alpha state. Use with care.

Prerequisites
-------------

Gencot assumes a Unix environment and the Haskell platform. It consists of a collection of Haskell programs and (Bourne) shell scripts which use standard Unix commands such as awk, sed, and others.

For installation you need the Haskell compiler (the latest tested ghc version is 8.10.4) and the Cabal build system.

Installation
------------

1. In a directory `G` clone this project (Gencot).
    This will yield `G/gencot`
2. In `G/gencot` execute

        git submodule init
        git submodule update
    This will clone the Cogent distribution into subdirectory `cogent`.
3. In `G/gencot` execute

        cabal new-update
    (if necessary) and then
    
        make
    This will compile all Haskell parts of Gencot and link them into `G/gencot/bin`.
4. Set environment variable `GENCOT_HOME` to `G/gencot`, e.g., by

        export GENCOT_HOME=G/gencot

Now you can use the commands

        gencot, items, parmod, auxcog
which are located in `G/gencot/bin` (by adding this directory to the command search path or by specifying the path when the command is invoked).

Note that this only builds the Gencot tool. If you also want to use the Cogent compiler you have to go to `G/gencot/cogent` and
build it as described there. For full support of all Gencot features build it using

        make INSTALL_FLAGS='--flags="+builtin-arrays"'

A quick check whether the installation was successful can be done as follows:

- if only Gencot has been built:
   Go to `G/gencot/examples/helloworld` and execute 

       make cogent
    It should run without apparent error messages.

- if also the Cogent compiler has been built:
   Go to `G/gencot/examples/helloworld` and execute

       make c
    It should run without apparent error messages.

- if also a C compiler is available:
   Go to `G/gencot/examples/helloworld` and execute 

       make cogent-run
    It should display "Hello World" in the last line.

Introduction
------------

Read the Gencot manual [manual/gencot-manual.pdf](manual/gencot-manual.pdf) (for easy access it is provided as a PDF file). 
It uses and explains the examples in subdirectory [examples](examples).

The concept and implementation is documented in [doc/gencot-devel.pdf](doc/gencot-devel.pdf).
