UNIT=part

HFILES = items.h
ifeq ($(UNIT), all)
CFILES = items.c alloc.c
COGOFILES = $(UNIT).o
else
CFILES = items.c
COGOFILES = $(UNIT).o alloc.o
endif

UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
PROPEDITFILES = ed-dflt-itemprops.done ed-ns-itemprops.done ed-nn-itemprops.done ed-glob-itemprops.done
MERGEFILES = merge-props.done
ACFILES = $(UNIT)-externs.ac $(UNIT)-manabstr.ac $(UNIT)-gencot.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
GENCOTFILES = $(UNIT)-gencot.h $(UNIT)-cogent-common.c 
IPHFILES = $(HFILES:.h=.h-itemprops) 
IPCFILES = $(CFILES:.c=.c-itemprops)
IPFILES = $(IPHFILES) $(IPCFILES)
IPUFILE = $(UNIT).unit-itemprops
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)
INCLPATH = -I.

binary: itemsbin
run: run-items
h-props: $(IPHFILES)
c-props: $(IPCFILES)
e-props: $(IPUFILE)
merge-props: merge-props.done
dflt-edit: ed-dflt-itemprops.done
ns-edit: ed-ns-itemprops.done
nn-edit: ed-nn-itemprops.done
glob-edit: ed-glob-itemprops.done
h-cogent: $(INCLFILES)
c-cogent: $(COGFILES)
cogent: ed-nn-itemprops.done $(COGSRC)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: cogent-items
cogent-run: run-cogent-items


.PHONY: clean

STDGUM=$(shell cogent --libgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"
# The following is used to fix a problem of some cpp implementations
CPPFIX = --cpp-args='-x c $$CPPIN -o $$CPPOUT -P'

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

$(IPUFILE): $(UNIT).unit $(UNIT)-external.items
ifeq ($(UNIT), all)
	items $(INCLPATH) unit > $(UNIT).unit-itemprops
else
	items $(INCLPATH) -u $(UNIT) unit > $(UNIT).unit-itemprops
endif

merge-props.done: $(IPHFILES) | ed-glob-itemprops.done
	for f in $(IPFILES); do \
	  items merge $$f $(IPUFILE) > iprops; \
	  mv iprops $(IPUFILE); \
	done
	cp $(IPUFILE) items.c-itemprops
	@touch merge-props.done

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

ed-dflt-itemprops.done: | $(IPHFILES)
	sed -i -e "s/int2P_t: /int2P_t: ro/;s|funLinPar1_t/1: ar|funLinPar1_t/1: |" items.h-itemprops
	@touch ed-dflt-itemprops.done

ed-ns-itemprops.done: | $(IPHFILES)
	sed -i -e "s/charCP_t: ro/charCP_t: ro ns/" items.h-itemprops
	@touch ed-ns-itemprops.done

ed-nn-itemprops.done: merge-props.done
	sed -i -e "s|allocInt/(): |allocInt/(): nn |;s|allocArr/(): |allocArr/(): nn |" items.c-itemprops
	sed -i -e "s|printAlloc/p1: ro ar|printAlloc/p1: ro ar nn|;s|printAlloc/p2: ro ar|printAlloc/p2: ro ar nn|" items.c-itemprops
	sed -i -e "s|allocInt/(): |allocInt/(): nn |;s|allocArr/(): |allocArr/(): nn |" $(IPUFILE)
	sed -i -e "s|printAlloc/p1: ro ar|printAlloc/p1: ro ar nn|;s|printAlloc/p2: ro ar|printAlloc/p2: ro ar nn|" $(IPUFILE)
	@touch ed-nn-itemprops.done

ed-glob-itemprops.done: | $(IPCFILES) $(IPUFILE)
	sed -i -e "s/printAlloc: /printAlloc: io/;s/main: /main: io hu/" items.c-itemprops
	sed -i -e "s/allocInt: /allocInt: hu/;s/allocArr: /allocArr: hu/;s/putchar: /putchar: io/;s/puts: /puts: io/" $(IPUFILE)
	sed -i -e "s|allocInt/(): |allocInt/(): ro|;s|allocArr/(): |allocArr/(): ro|" $(IPUFILE)
	@touch ed-glob-itemprops.done

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): ed-nn-itemprops.done $(COGSRC) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(COGPPARGS) $(UNIT).cogent --infer-c-funcs="$(ACFILES)" $(CPPFIX)

# Implicitly also generates $(ACFILESC)
$(UNIT).c: $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit
ifeq ($(UNIT), all)
	auxcog $(INCLPATH) unit
else
	auxcog $(INCLPATH) -u $(UNIT) unit
endif

$(UNIT)-gencot.h:
	@cp $(GENCOTC)/gencot.h $@

$(UNIT)-cogent-common.c:
	@cp $(GENCOTC)/cogent-common.c $@

$(UNIT)-gencot.ac:
	@cp $(GENCOTC)/gencot.ac $@

$(UNIT).o: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(GENCOTFILES) $(ACFILESC) $(COGHFILES)
	$(CC) -c $(INCLPATH) $(UNIT).c

cogent-items: $(COGOFILES)
	$(CC) -o cogent-items $(COGOFILES)

run-cogent-items: cogent-items
	./cogent-items

clean:
	-rm -rf comments
	-rm -f itemsbin
	-rm -f $(IPFILES) $(UNIT).unit-itemprops
	-rm -f $(COGSRC) $(UNIT)-external.items $(CFILES:.c=-entry.ac)
	-rm -f $(MERGEFILES) $(PROPEDITFILES)
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f $(UNIT).c $(GENCOTFILES) $(ACFILESC) $(UNIT)-gencot.ac
	-rm -f $(OFILES) $(COGOFILES) cogent-items
