UNIT=all

HFILES = 
CFILES = types.c
UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
EDITFILES = ed-types.done ed-$(UNIT)-dvdtypes.done
ACFILES = $(UNIT)-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
GENCOTFILES = $(UNIT)-gencot.h $(UNIT)-cogent-common.c 
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)
INCLPATH =

binary: $(OFILES)
cogent: $(COGSRC)
edit: $(EDITFILES)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: $(UNIT).o

.PHONY: clean 

STDGUM=$(shell cogent --libgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

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

$(UNITFILES): $(UNIT).unit $(UNIT)-external.items $(CFILES)
ifeq ($(UNIT), all)
	gencot $(INCLPATH) unit
else
	gencot $(INCLPATH) -u $(UNIT) unit
endif

ed-types.done: types.cogent
	sed -i -e "9,10d;57d" types.cogent
	@touch ed-types.done

ed-$(UNIT)-dvdtypes.done: $(UNIT)-dvdtypes.cogent
	sed -i -e "28,29d;31,32d" $(UNIT)-dvdtypes.cogent
	@touch ed-$(UNIT)-dvdtypes.done

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(COGPPARGS) $(UNIT).cogent --infer-c-funcs="$(ACFILES)"

$(UNIT).c $(UNIT)-macros.h $(ACFILESC): $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit
	auxcog unit

$(UNIT)-gencot.h:
	@cp $(GENCOTC)/gencot.h $@

$(UNIT)-cogent-common.c:
	@cp $(GENCOTC)/cogent-common.c $@

$(UNIT).o: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT)-macros.h $(GENCOTFILES) $(ACFILESC)
	cc -c -I$(STDGUM) -I$(GENCOTC) $(UNIT).c

clean:
	-rm -f $(COGSRC) $(UNIT)-external.items types-entry.ac
	-rm -f $(EDITFILES)
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f $(UNIT).c $(UNIT)-macros.h $(GENCOTFILES) $(ACFILESC)
	-rm -f $(OFILES) $(UNIT).o
