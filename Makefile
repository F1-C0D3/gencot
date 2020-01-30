all: build links

build: check deccm pmext pmgen pmprc trans extns exttp dvdtp cgrph dmpca

CHECK = gencot-check
TRANS = gencot-translate
DECCM = gencot-deccomments
EXTNS = gencot-externs
EXTTP = gencot-exttypes
DVDTP = gencot-dvdtypes
PMEXT = parmod-externs
PMGEN = parmod-gen
PMPRC = parmod-proc
CGRPH = callgraph-print
DMPCA = dump-c-ast

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

pmext: 
	cabal new-build $(PMEXT)

pmgen: 
	cabal new-build $(PMGEN)

pmprc: 
	cabal new-build $(PMPRC)

cgrph: 
	cabal new-build $(CGRPH)

dmpca: 
	cabal new-build $(DMPCA)

links: bin/$(CHECK) bin/$(DECCM) bin/$(PMEXT) bin/$(PMGEN) bin/$(PMPRC) bin/$(TRANS) bin/$(EXTNS) bin/$(EXTTP) bin/$(DVDTP) bin/$(CGRPH) bin/$(DMPCA)

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

bin/$(PMEXT):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMEXT)/build/$(PMEXT)/$(PMEXT) .)

bin/$(PMGEN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMGEN)/build/$(PMGEN)/$(PMGEN) .)

bin/$(PMPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMPRC)/build/$(PMPRC)/$(PMPRC) .)

bin/$(CGRPH):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CGRPH)/build/$(CGRPH)/$(CGRPH) .)

bin/$(DMPCA):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DMPCA)/build/$(DMPCA)/$(DMPCA) .)
