all: build links

build: check deccm pmgen pmprc trans entrs extns exttp dvdtp cgrph dmpca cgprc itprc itgen ituse itext itefs actis actif acgop

CHECK = gencot-check
TRANS = gencot-translate
ENTRS = gencot-entries
DECCM = gencot-deccomments
EXTNS = gencot-externs
EXTTP = gencot-exttypes
DVDTP = gencot-dvdtypes
PMGEN = parmod-gen
PMPRC = parmod-proc
CGRPH = callgraph-print
DMPCA = dump-c-ast
CGPRC = cogent-proc
ITPRC = items-proc
ITGEN = items-gen
ITUSE = items-used
ITEXT = items-externs
ITEFS = items-extfuns
ACTIS = auxcog-ctypstruct
ACTIF = auxcog-ctypfunc
ACGOP = auxcog-genops

check: 
	cabal new-build $(CHECK)

trans: 
	cabal new-build $(TRANS)

entrs: 
	cabal new-build $(ENTRS)

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

cgprc: 
	cabal new-build $(CGPRC)

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

actis: 
	cabal new-build $(ACTIS)

actif: 
	cabal new-build $(ACTIF)

acgop: 
	cabal new-build $(ACGOP)

links: bin/$(CHECK) bin/$(DECCM) bin/$(PMGEN) bin/$(PMPRC) bin/$(TRANS) bin/$(ENTRS) bin/$(EXTNS) bin/$(EXTTP) bin/$(DVDTP) bin/$(CGRPH) bin/$(DMPCA) bin/$(CGPRC) bin/$(ITPRC) bin/$(ITGEN) bin/$(ITUSE) bin/$(ITEXT) bin/$(ITEFS) bin/$(ACTIS) bin/$(ACTIF) bin/$(ACGOP)

bin/$(CHECK):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CHECK)/build/$(CHECK)/$(CHECK) .)

bin/$(TRANS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(TRANS)/build/$(TRANS)/$(TRANS) .)

bin/$(ENTRS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ENTRS)/build/$(ENTRS)/$(ENTRS) .)

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

bin/$(CGPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CGPRC)/build/$(CGPRC)/$(CGPRC) .)

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

bin/$(ACTIS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ACTIS)/build/$(ACTIS)/$(ACTIS) .)

bin/$(ACTIF):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ACTIF)/build/$(ACTIF)/$(ACTIF) .)

bin/$(ACGOP):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ACGOP)/build/$(ACGOP)/$(ACGOP) .)
