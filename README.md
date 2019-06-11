Gencot
======

Gencot is the tool for translating C code to Cogent developed and used in HoBit
for translating mbedTLS (at least partially)
to Cogent.

Current status
--------------

- most of the design documented in `doc/`
- most filter scripts implemented in `bin/`
- main translation implemented in `src/`
- parameter modification analysis tool implemented in `src/`

Installation
------------

1. If not yet done, get the Cogent distribution from GitHub: In a directory `D` execute

        git clone https://github.com/NICTA/cogent.git
    This will yield `D/cogent`
2. In a directory `G` clone this project (Gencot).  
    This will yield `G/gencot`
3. adapt the two paths in `G/gencot/cabal.project` to point to  
  `D/cogent/cogent`  
  and  
  `D/cogent/isa-parser`
4. In `G/gencot` execute

        make
5. Set environment variable `GENCOT_HOME` to `G/gencot`, e.g., by

        export GENCOT_HOME=G/gencot

Now you can use the command

    parmod
which is located in `G/gencot/bin` (it need not be in the command search path).
