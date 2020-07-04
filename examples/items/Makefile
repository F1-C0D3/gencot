UNIT=part

HFILES = items.h
ifeq ($(UNIT), all)
CFILES = items.c alloc.c
else
CFILES = items.c
endif

UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
EDITFILES = ed-items.done
PROPEDITFILES = ed-dflt-itemprops.done ed-ns-itemprops.done ed-nn-itemprops.done
ACFILES = $(UNIT)-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
IPHFILES = $(HFILES:.h=.h-itemprops) 
IPCFILES = $(CFILES:.c=.c-itemprops)
IPFILES = $(IPHFILES) $(IPCFILES)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)
INCLPATH = -I.

binary: itemsbin
run: run-items
h-props: $(IPHFILES)
c-props: $(IPCFILES)
e-props: external-props
dflt-edit: ed-dflt-itemprops.done
ns-edit: ed-ns-itemprops.done
nn-edit: ed-nn-itemprops.done
h-cogent: $(INCLFILES)
props: $(UNIT).unit-itemprops
cogent: $(COGSRC)
edit: $(EDITFILES)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: $(UNIT).o

.PHONY: clean external-props

STDGUM=$(shell cogent --stdgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

itemsbin: $(OFILES)
	$(CC) -o itemsbin $(OFILES)

run-items: itemsbin
	./itemsbin

$(UNIT)-external.items: $(UNIT).unit
ifeq ($(UNIT), all)
	items $(INCLPATH) used
else
	items $(INCLPATH) -u $(UNIT) used
endif

external-props: $(UNIT).unit $(UNIT)-external.items
ifeq ($(UNIT), all)
	items $(INCLPATH) unit
else
	items $(INCLPATH) -u $(UNIT) unit
endif

$(UNIT).unit-itemprops: $(IPFILES) $(UNIT).unit $(UNIT)-external.items
ifeq ($(UNIT), all)
	items $(INCLPATH) unit > $(UNIT).unit-itemprops
else
	items $(INCLPATH) -u $(UNIT) unit > $(UNIT).unit-itemprops
endif
	for f in $(IPFILES); do \
	  items merge $$f $(UNIT).unit-itemprops > iprops; \
	  mv iprops $(UNIT).unit-itemprops; \
	done

%-itemprops: %
	items $(INCLPATH) file $* > $*-itemprops

%-incl.cogent: %.h $(UNIT)-external.items
ifeq ($(UNIT), all)
	gencot hfile $*.h
else
	gencot -u $(UNIT) hfile $*.h
endif

# depends on $(INCLFILES) for comment transfer from declarations
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

ed-items.done: items.cogent
	sed -i -e "15,16d;17s/f(/f0(/;18s/->/./;19s/-}/(0, argv)/" items.cogent
	sed -i -e "6,7d;8s/*p1/getPtr p1/;8s/f(/f1(/;9s/p2\[0]/getArr(p2,0)/;9s/p2\[1]/getArr(p2,1)/;9s/p2\[2]/getArr(p2,2)/;9s/f(/f3(/;10s/-}/()/" items.cogent
	@touch ed-items.done

ed-dflt-itemprops.done: items.h-itemprops
	sed -i -e "s/intP_t: /intP_t: ro/;s|funLinPar1_t/1: ar|funLinPar1_t/1: |" items.h-itemprops
	@touch ed-dflt-itemprops.done

ed-ns-itemprops.done: items.h-itemprops
	sed -i -e "s/charCP_t: ro/charCP_t: ro ns/" items.h-itemprops
	@touch ed-ns-itemprops.done

ed-nn-itemprops.done: items.h-itemprops
	sed -i -e "s/sphereC.center: ro/sphereC.center: ro nn/" items.h-itemprops
	@touch ed-nn-itemprops.done

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(COGPPARGS) $(UNIT).cogent --infer-c-funcs="$(ACFILES)"

# Implicitly also generates $(ACFILESC)
$(UNIT).c $(UNIT)-macros.h: $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit
ifeq ($(UNIT), all)
	auxcog unit
else
	auxcog -u $(UNIT) unit
endif

$(UNIT).o: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT)-macros.h $(ACFILESC)
	cc -c -I$(STDGUM) -I$(GENCOTC) $(UNIT).c

clean:
	-rm -rf comments
	-rm -f itemsbin
	-rm -f $(IPFILES) $(UNIT).unit-itemprops
	-rm -f $(COGSRC) $(UNIT)-external.items $(CFILES:.c=-entry.ac)
	-rm -f $(EDITFILES) $(PROPEDITFILES)
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f $(UNIT).c $(UNIT)-macros.h $(ACFILESC)
	-rm -f $(OFILES) $(UNIT).o
