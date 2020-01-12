UNITFILES = unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit.cogent
EDUNITFILES = ed-unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit-externs.ac
ACFILES = unit-externs.ac hello-entry.ac
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)

binary: hello
run: run-hello
cogent: hello.cogent $(UNITFILES)
edit: ed-hello.cogent $(EDUNITFILES)
cogent-c: gen-unit.c gen-unit.h
cogent-binary: cogent-hello
cogent-run: run-cogent-hello

.PHONY: clean run-hello run-cogent-hello

STDGUM=$(shell cogent --stdgum-dir)

run-hello: hello
	./hello

hello.cogent: hello.c
	gencot cfile hello.c

$(UNITFILES): unit.files hello.c
	gencot unit unit.files

ed-hello.cogent: hello.cogent
	sed -e "4,5d;7d;s/;/; 0/" hello.cogent > ed-hello.cogent

ed-unit-externs.cogent: unit-externs.cogent
	sed -e "s/(CPtr U8)\!/String/" unit-externs.cogent > ed-unit-externs.cogent

gen-unit.c gen-unit.h: unit.cogent ed-hello.cogent hello-entry.ac $(EDUNITFILES)
	cogent -o gen-unit -g unit.cogent --infer-c-funcs="$(ACFILES)"

cogent-hello: unit.c gen-unit.c gen-unit.h $(ACFILESINF)
	cc -o cogent-hello -I$(STDGUM) unit.c

run-cogent-hello: cogent-hello
	./cogent-hello

clean:
	-rm -f hello
	-rm -f hello.cogent unit-*.cogent
	-rm -f ed-hello.cogent ed-unit-*.cogent
	-rm -f gen-unit.c gen-unit.h $(ACFILESPP) $(ACFILESINF)
	-rm -f cogent-hello
