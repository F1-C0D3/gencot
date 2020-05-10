HFILES = items.h
CFILES = items.c alloc.c
PCFILES = items.c
UNITFILES = part-externs.cogent part-exttypes.cogent part-dvdtypes.cogent part.cogent
EDITFILES = ed-items.done
PROPEDITFILES = ed-dflt-itemprops.done ed-ns-itemprops.done ed-nn-itemprops.done
ACFILES = part-externs.ac $(PCFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
IPHFILES = $(HFILES:.h=.h-itemprops) 
IPCFILES = $(PCFILES:.c=.c-itemprops)
IPFILES = $(IPHFILES) $(IPCFILES)
OFILES = $(CFILES:.c=.o)
COGFILES = $(PCFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

binary: itemsbin
run: run-items
h-itemprops: $(IPHFILES)
c-itemprops: $(IPCFILES)
e-itemprops: part.ext-itemprops
dflt-edit: ed-dflt-itemprops.done
ns-edit: ed-ns-itemprops.done
nn-edit: ed-nn-itemprops.done
h-cogent: $(INCLFILES)
part-itemprops: part.unit-itemprops
part-cogent: $(COGSRC)
part-edit: $(EDITFILES)
part-c: part-gen.c part-gen.h part.c
part-binary: part.o

.PHONY: clean 

STDGUM=$(shell cogent --stdgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

itemsbin: $(OFILES)
	$(CC) -o itemsbin $(OFILES)

run-items: itemsbin
	./itemsbin

part.ext-itemprops: part.unit
	items -I. -u part unit > part.ext-itemprops

part.unit-itemprops: $(IPFILES) part.ext-itemprops
	cp part.ext-itemprops part.unit-itemprops
	for f in $(IPFILES); do \
	  items merge $$f part.unit-itemprops > iprops; \
	  mv iprops part.unit-itemprops; \
	done

%-itemprops: %
	items -I. file $* > $*-itemprops

%-incl.cogent: %.h
	gencot hfile $*.h

%.cogent: %.c
	gencot -I. cfile $*.c

$(UNITFILES): part.unit $(CFILES)
	gencot -I. -u part unit

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

part-gen.c part-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o part-gen -g $(COGPPARGS) part.cogent --infer-c-funcs="$(ACFILES)"

part.c part-macros.h $(ACFILESC): part-gen.c part-gen.h $(ACFILESINF) part.unit
	auxcog -u part unit

part.o: part.c part-gen.c part-gen.h part-macros.h $(ACFILESC)
	cc -c -I$(STDGUM) -I$(GENCOTC) part.c

clean:
	-rm -rf comments
	-rm -f itemsbin
	-rm -f $(IPFILES) part.ext-itemprops part.unit-itemprops
	-rm -f $(COGSRC)
	-rm -f $(EDITFILES) $(PROPEDITFILES)
	-rm -f part-gen.c part-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f part.c part-macros.h $(ACFILESC)
	-rm -f $(OFILES) part.o
