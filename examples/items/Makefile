HFILES = items.h
CFILES = items.c alloc.c
PCFILES = items.c
UNITFILES = part-externs.cogent part-exttypes.cogent part-dvdtypes.cogent part.cogent
EDITFILES = ed-items.done
ACFILES = part-externs.ac $(PCFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
IPFILES = $(HFILES:.h=.h-itemprops) $(PCFILES:.c=.c-itemprops)
OFILES = $(CFILES:.c=.o)
COGFILES = $(PCFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

binary: itemsbin
run: run-items
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
	items -I. unit part.unit > part.ext-itemprops

part.unit-itemprops: $(IPFILES) part.ext-itemprops
	cp part.ext-itemprops part.unit-itemprops
	for f in $(IPFILES); do \
	  items merge $$f part.unit-itemprops > iprops; \
	  mv iprops part.unit-itemprops; \
	done

%-itemprops: %
	items -I. file $* > $*-itemprops

%-incl.cogent: %.h %.h-itemprops
	gencot hfile $*.h

%.cogent: %.c %.c-itemprops
	gencot -I. cfile $*.c

$(UNITFILES): part.unit $(CFILES) part.unit-itemprops
	gencot -I. unit part.unit

ed-items.done: items.cogent
	sed -i -e "15,16d;17s/f(/f0(/;18s/->/./;19s/-}/(0, argv)/" items.cogent
	sed -i -e "6,7d;8s/*p1/getPtr p1/;8s/f(/f1(/;9s/p2\[0]/getArr(p2,0)/;9s/p2\[1]/getArr(p2,1)/;9s/p2\[2]/getArr(p2,2)/;9s/f(/f3(/;10s/-}/()/" items.cogent
	@touch ed-items.done

part-gen.c part-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o part-gen -g $(COGPPARGS) part.cogent --infer-c-funcs="$(ACFILES)"

part.c part-macros.h $(ACFILESC): part-gen.c part-gen.h $(ACFILESINF) part.unit
	auxcog unit part.unit

part.o: part.c part-gen.c part-gen.h part-macros.h $(ACFILESC)
	cc -c -I$(STDGUM) -I$(GENCOTC) part.c

clean:
	-rm -rf comments
	-rm -f itemsbin
	-rm -f $(IPFILES) part.ext-itemprops part.unit-itemprops
	-rm -f $(COGSRC)
	-rm -f $(EDITFILES)
	-rm -f part-gen.c part-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f part.c part-macros.h $(ACFILESC)
	-rm -f $(OFILES) part.o
