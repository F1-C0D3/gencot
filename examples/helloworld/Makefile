UNIT=all

HFILES = 
CFILES = hello.c
UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
ACFILES = $(UNIT)-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
GENCOTFILES = $(UNIT)-gencot.h $(UNIT)-cogent-common.c
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)
COGHFILES = cogent-defns.h cogent-endianness.h
INCLPATH =

binary: hello
run: run-hello
cogent: $(COGSRC)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: cogent-hello
cogent-run: run-cogent-hello

.PHONY: clean run-hello run-cogent-hello

STDGUM=$(shell cogent --libgum-dir)
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"
# The following is used to fix a problem of some cpp implementations
CPPFIX = --cpp-args='-x c $$CPPIN -o $$CPPOUT -P'

run-hello: hello
	./hello

$(UNIT)-external.items: $(UNIT).unit
ifeq ($(UNIT), all)
	items $(INCLPATH) used
else
	items $(INCLPATH) -u $(UNIT) used
endif

%-incl.cogent: %.h $(UNIT)-external.items
ifeq ($(UNIT), all)
	gencot hfile $*.h
else
	gencot -u $(UNIT) hfile $*.h
endif

%.cogent: %.c %.c-itemprops $(UNIT)-external.items
ifeq ($(UNIT), all)
	gencot $(INCLPATH) cfile $*.c
else
	gencot $(INCLPATH) -u $(UNIT) cfile $*.c
endif

$(UNITFILES): $(UNIT).unit $(UNIT).unit-itemprops $(UNIT)-external.items $(CFILES) common.gencot-std
ifeq ($(UNIT), all)
	gencot $(INCLPATH) unit
else
	gencot $(INCLPATH) -u $(UNIT) unit
endif

$(COGHFILES):
	@for f in $(COGHFILES); do \
	  cp $(STDGUM)/$$f .; \
	done

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): $(COGSRC) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(UNIT).cogent --infer-c-funcs="$(ACFILES)" $(CPPFIX)


$(UNIT).c $(ACFILESC) $(GENCOTFILES): $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit $(COGHFILES)
ifeq ($(UNIT), all)
	auxcog -I. unit
else
	auxcog -I. -u $(UNIT) unit
endif

cogent-hello: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(GENCOTFILES) $(ACFILESC)
	cc -o cogent-hello -I. $(UNIT).c

run-cogent-hello: cogent-hello
	./cogent-hello

clean:
	-rm -f hello
	-rm -f $(COGSRC) $(UNIT)-external.items hello-entry.ac
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f $(UNIT).c $(GENCOTFILES) $(ACFILESC) $(COGHFILES)
	-rm -f cogent-hello
