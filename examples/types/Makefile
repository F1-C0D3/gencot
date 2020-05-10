HFILES = 
CFILES = types.c
UNITFILES = all-externs.cogent all-exttypes.cogent all-dvdtypes.cogent all.cogent
EDITFILES = ed-types.done ed-all-dvdtypes.done
ACFILES = all-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

binary: $(OFILES)
all-cogent: $(COGSRC)
all-edit: $(EDITFILES)
all-c: all-gen.c all-gen.h all.c
all-binary: all.o

.PHONY: clean 

STDGUM=$(shell cogent --stdgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

%-incl.cogent: %.h
	gencot hfile $*.h

%.cogent: %.c
	gencot cfile $*.c

$(UNITFILES): all.unit $(CFILES)
	gencot unit

ed-types.done: types.cogent
	sed -i -e "9,10d;57d" types.cogent
	@touch ed-types.done

ed-all-dvdtypes.done: all-dvdtypes.cogent
	sed -i -e "28,29d;31,32d" all-dvdtypes.cogent
	@touch ed-all-dvdtypes.done

all-gen.c all-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o all-gen -g $(COGPPARGS) all.cogent --infer-c-funcs="$(ACFILES)"

all.c all-macros.h $(ACFILESC): all-gen.c all-gen.h $(ACFILESINF) all.unit
	auxcog unit

all.o: all.c all-gen.c all-gen.h all-macros.h $(ACFILESC)
	cc -c -I$(STDGUM) -I$(GENCOTC) all.c

clean:
	-rm -f $(COGSRC)
	-rm -f $(EDITFILES)
	-rm -f all-gen.c all-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f all.c all-macros.h $(ACFILESC)
	-rm -f $(OFILES) all.o
