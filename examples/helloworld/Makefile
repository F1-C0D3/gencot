UNIT=all

HFILES = 
CFILES = hello.c
UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
EDITFILES = ed-hello.done
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

binary: hello
run: run-hello
cogent: $(COGSRC)
edit: $(EDITFILES)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: cogent-hello
cogent-run: run-cogent-hello

.PHONY: clean run-hello run-cogent-hello

STDGUM=$(shell cogent --libgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

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

%.c-itemprops: itemprops
	@cp itemprops $@

$(UNITFILES): $(UNIT).unit $(UNIT).unit-itemprops $(UNIT)-external.items $(CFILES) common.gencot-std
ifeq ($(UNIT), all)
	gencot $(INCLPATH) unit
else
	gencot $(INCLPATH) -u $(UNIT) unit
endif

common.gencot-std:
	echo "common: common" > $@

ed-hello.done: hello.cogent
	sed -i -e "4,5d;7d;s/;/; 0/" hello.cogent
	@touch ed-hello.done

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): $(COGSRC) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(UNIT).cogent --infer-c-funcs="$(ACFILES)"

$(UNIT).c $(UNIT)-macros.h $(ACFILESC): $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit
ifeq ($(UNIT), all)
	auxcog unit
else
	auxcog -u $(UNIT) unit
endif

$(UNIT)-gencot.h:
	@cp $(GENCOTC)/gencot.h $@

$(UNIT)-cogent-common.c:
	@cp $(GENCOTC)/cogent-common.c $@

$(UNIT).unit-itemprops: itemprops
	@cp itemprops $@

cogent-hello: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT)-macros.h $(GENCOTFILES) $(ACFILESC)
	cc -o cogent-hello -I$(STDGUM) -I$(GENCOTC) $(UNIT).c

run-cogent-hello: cogent-hello
	./cogent-hello

clean:
	-rm -f hello
	-rm -f $(COGSRC) $(UNIT)-external.items hello-entry.ac
	-rm -f $(EDITFILES)
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f $(UNIT).c $(UNIT)-macros.h $(GENCOTFILES) $(ACFILESC)
	-rm -f cogent-hello $(UNIT).unit-itemprops *.c-itemprops common.gencot-std
