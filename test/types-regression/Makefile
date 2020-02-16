GC=../../bin/gencot
PM=../../bin/parmod
IT=../../bin/items

TESTS = prim enum struct union array func parmod pointer names const
UNIT = externs exttypes dvdtypes
ABSINCL = -I/home/teege/work/projekte/code/HoBit/devel/gencot/test/types-regression

compile: $(foreach TST,$(TESTS),types-$(TST).o)

cogent: $(foreach TST,$(TESTS),types-$(TST).cogent) unit

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -f test.unit test.cogent $(foreach U,$(UNIT),test-$(U).cogent)
	-rm -f types-parmod.json-itemprops  # types-pointer.c-itemprops test.unit-itemprops
	-rm -f test.gencot-extitems test.ext-dfltprops

types-parmod.json-itemprops: types-parmod.json
	$(PM) out types-parmod.json > types-parmod.json-itemprops

#%-itemprops: %-manprops types-parmod.json-itemprops
#	$(IT) mergeto $*-manprops types-parmod.json-itemprops > $*-itemprops

types-parmod.cogent: types-parmod.c
	$(GC) cfile types-parmod.c types-parmod.json

types-pointer.cogent: types-pointer.c types-pointer.c-itemprops
	$(GC) cfile types-pointer.c

unit-regression: unit $(foreach U,$(UNI),test-$(U)-expected.cogent)
	-@for u in $(UNIT); do \
	  echo "diff test-$$u.cogent test-$$u-expected.cogent"; \
	  diff test-$$u.cogent test-$$u-expected.cogent; \
	done
	-diff test.gencot-extitems test-expected.gencot-extitems
	-diff test.ext-dfltprops test-expected.ext-dfltprops

unit-expect-current: unit
	@for u in $(UNIT); do \
	  echo "cp test-$$u.cogent test-$$u-expected.cogent"; \
	  cp test-$$u.cogent test-$$u-expected.cogent; \
	done
	@cp test.gencot-extitems test-expected.gencot-extitems
	@cp test.ext-dfltprops test-expected.ext-dfltprops

%.cogent: %.c
	$(GC) cfile $*.c

%-regression: types-%.cogent types-%-expected.cogent
	-diff types-$*.cogent types-$*-expected.cogent

%-expect-current: types-%.cogent
	cp types-$*.cogent types-$*-expected.cogent

%-clean:
	-rm -f types-$*.cogent types-$*.o

test.unit: 
	@for f in $(foreach TST,$(TESTS),types-$(TST).c); do \
	  echo $$f >> test.unit; \
	done
	@echo extrefs.c >> test.unit
	@cat test.unit

unit: test.unit test.unit-itemprops test.gencot-manitems
	$(IT) $(ABSINCL) used test.unit > test.gencot-extitems
	$(IT) $(ABSINCL) unit test.unit > test.ext-dfltprops
	$(GC) $(ABSINCL) unit test.unit types-parmod.json
