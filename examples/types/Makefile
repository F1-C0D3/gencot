UNIT=all

HFILES = 
CFILES = types.c
UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
EDITFILES = ed-types.done ed-$(UNIT)-dvdtypes.done
ACFILES = $(UNIT)-externs.ac $(CFILES:.c=-entry.ac) $(UNIT)-gencot.ac
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
GENCOTFILES = $(UNIT)-gencot.h $(UNIT)-cogent-common.c 
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)
COGHFILES = cogent-defns.h cogent-endianness.h
# Include path used for original and generated C program
INCLPATH = -I.

binary: $(OFILES)
cogent: $(COGSRC)
edit: $(EDITFILES)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: $(UNIT).o

.PHONY: clean 

STDGUM=$(shell cogent --libgum-dir)
GENCOTI=$(GENCOT_HOME)/include
GENCOTC=$(GENCOT_HOME)/c
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"
# The following is used to fix a problem of some cpp implementations
CPPFIX = --cpp-args='-x c $$CPPIN -o $$CPPOUT -P'

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

%.cogent: %.c $(UNIT)-external.items $(INCLFILES)
ifeq ($(UNIT), all)
	gencot $(INCLPATH) cfile $*.c
else
	gencot $(INCLPATH) -u $(UNIT) cfile $*.c
endif

$(UNITFILES): $(UNIT).unit $(UNIT)-external.items $(CFILES) common.gencot-std
ifeq ($(UNIT), all)
	gencot $(INCLPATH) unit
else
	gencot $(INCLPATH) -u $(UNIT) unit
endif

ed-types.done: types.cogent
	sed -i -e "9,10d;60,61d" types.cogent
	@touch ed-types.done

ed-$(UNIT)-dvdtypes.done: $(UNIT)-dvdtypes.cogent
	sed -i -e "25,26d;28,29d" $(UNIT)-dvdtypes.cogent
	@touch ed-$(UNIT)-dvdtypes.done

$(UNIT)-gencot.ac:
	cp $(GENCOTC)/gencot.ac $(UNIT)-gencot.ac

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(UNIT).cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)" $(CPPFIX)

$(UNIT).c $(ACFILESC) $(GENCOTFILES): $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit $(COGHFILES)
ifeq ($(UNIT), all)
	auxcog $(INCLPATH) unit
else
	auxcog $(INCLPATH) -u $(UNIT) unit
endif

$(UNIT).o: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(GENCOTFILES) $(ACFILESC) $(COGHFILES)
	cc -c $(INCLPATH) $(UNIT).c

clean:
	-rm -f $(COGSRC) $(UNIT)-external.items types-entry.ac
	-rm -f $(EDITFILES)
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF) $(UNIT)-gencot.ac
	-rm -f $(UNIT).c $(GENCOTFILES) $(ACFILESC)
	-rm -f $(OFILES) $(UNIT).o
