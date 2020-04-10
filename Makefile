all: build links

build: check deccm pmgen pmprc trans extns exttp dvdtp cgrph dmpca itprc itgen ituse itext itefs

CHECK = gencot-check
TRANS = gencot-translate
DECCM = gencot-deccomments
EXTNS = gencot-externs
EXTTP = gencot-exttypes
DVDTP = gencot-dvdtypes
PMGEN = parmod-gen
PMPRC = parmod-proc
CGRPH = callgraph-print
DMPCA = dump-c-ast
ITPRC = items-proc
ITGEN = items-gen
ITUSE = items-used
ITEXT = items-externs
ITEFS = items-extfuns

check: 
	cabal new-build $(CHECK)

trans: 
	cabal new-build $(TRANS)

deccm: 
	cabal new-build $(DECCM)

extns: 
	cabal new-build $(EXTNS)

exttp: 
	cabal new-build $(EXTTP)

dvdtp: 
	cabal new-build $(DVDTP)

pmgen: 
	cabal new-build $(PMGEN)

pmprc: 
	cabal new-build $(PMPRC)

cgrph: 
	cabal new-build $(CGRPH)

dmpca: 
	cabal new-build $(DMPCA)

itprc: 
	cabal new-build $(ITPRC)

itgen: 
	cabal new-build $(ITGEN)

ituse: 
	cabal new-build $(ITUSE)

itext: 
	cabal new-build $(ITEXT)

itefs: 
	cabal new-build $(ITEFS)

links: bin/$(CHECK) bin/$(DECCM) bin/$(PMGEN) bin/$(PMPRC) bin/$(TRANS) bin/$(EXTNS) bin/$(EXTTP) bin/$(DVDTP) bin/$(CGRPH) bin/$(DMPCA) bin/$(ITPRC) bin/$(ITGEN) bin/$(ITUSE) bin/$(ITEXT) bin/$(ITEFS)

bin/$(CHECK):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CHECK)/build/$(CHECK)/$(CHECK) .)

bin/$(TRANS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(TRANS)/build/$(TRANS)/$(TRANS) .)

bin/$(DECCM):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DECCM)/build/$(DECCM)/$(DECCM) .)

bin/$(EXTNS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTNS)/build/$(EXTNS)/$(EXTNS) .)

bin/$(EXTTP):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTTP)/build/$(EXTTP)/$(EXTTP) .)

bin/$(DVDTP):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DVDTP)/build/$(DVDTP)/$(DVDTP) .)

bin/$(PMGEN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMGEN)/build/$(PMGEN)/$(PMGEN) .)

bin/$(PMPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMPRC)/build/$(PMPRC)/$(PMPRC) .)

bin/$(CGRPH):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CGRPH)/build/$(CGRPH)/$(CGRPH) .)

bin/$(DMPCA):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DMPCA)/build/$(DMPCA)/$(DMPCA) .)

bin/$(ITPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ITPRC)/build/$(ITPRC)/$(ITPRC) .)

bin/$(ITGEN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ITGEN)/build/$(ITGEN)/$(ITGEN) .)

bin/$(ITUSE):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ITUSE)/build/$(ITUSE)/$(ITUSE) .)

bin/$(ITEXT):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ITEXT)/build/$(ITEXT)/$(ITEXT) .)

bin/$(ITEFS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ITEFS)/build/$(ITEFS)/$(ITEFS) .)
