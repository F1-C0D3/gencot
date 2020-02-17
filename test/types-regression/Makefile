GC=../../bin/gencot
PM=../../bin/parmod
IT=../../bin/items

TESTS = prim enum struct union array func parmod pointer names const
UNIT = externs exttypes dvdtypes
ABSINCL = -I/home/teege/work/projekte/code/HoBit/devel/gencot/test/types-regression
AUNIT = gencot-extitems ext-dfltprops

compile: $(foreach TST,$(TESTS),types-$(TST).o)

cogent: $(foreach TST,$(TESTS),types-$(TST).cogent) unit

dfltprops: $(foreach TST,$(TESTS),types-$(TST).c-dfltprops) test.ext-dfltprops

itemprops: $(foreach TST,$(TESTS),types-$(TST).c-itemprops) test.ext-itemprops

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -f test.unit test.cogent $(foreach U,$(UNIT),test-$(U).cogent)
	-rm -f types-parmod.json-itemprops  # types-pointer.c-itemprops test.unit-itemprops
	-rm -f test.gencot-extitems test.ext-dfltprops test.ext-itemprops test.unit-itemprops

types-parmod.json-itemprops: types-parmod.json
	$(PM) out types-parmod.json > types-parmod.json-itemprops

types-pointer.c-itemprops: types-pointer.c-manprops types-pointer.c-dfltprops types-parmod.json-itemprops
	$(IT) mergeto types-pointer.c-dfltprops types-parmod.json-itemprops > types-pointer.c-hprops
	$(IT) mergeto types-pointer.c-hprops types-pointer.c-manprops > types-pointer.c-itemprops
	rm types-pointer.c-hprops

%-itemprops: %-dfltprops types-parmod.json-itemprops
	$(IT) mergeto $*-dfltprops types-parmod.json-itemprops > $*-itemprops

types-parmod.cogent: types-parmod.c
	$(GC) cfile types-parmod.c types-parmod.json

types-pointer.cogent: types-pointer.c types-pointer.c-itemprops
	$(GC) cfile types-pointer.c

unit-regression: unit $(foreach U,$(UNIT),test-$(U)-expected.cogent) $(foreach U,$(AUNIT),test.$(U) test-expected.$(U))
	-@for u in $(UNIT); do \
	  echo "diff test-$$u.cogent test-$$u-expected.cogent"; \
	  diff test-$$u.cogent test-$$u-expected.cogent; \
	done
	-@for u in $(AUNIT); do \
	  echo "diff test.$$u test-expected.$$u"; \
	  diff test.$$u test-expected.$$u; \
	done

unit-expect-current: unit
	@for u in $(UNIT); do \
	  echo "cp test-$$u.cogent test-$$u-expected.cogent"; \
	  cp test-$$u.cogent test-$$u-expected.cogent; \
	done
	@for u in $(AUNIT); do \
	  echo "cp test.$$u test-expected.$$u"; \
	  cp test.$$u test-expected.$$u; \
	done

test.ext-dfltprops: test.unit test.gencot-manitems
	$(IT) $(ABSINCL) unit test.unit > test.ext-dfltprops

test.gencot-extitems: test.unit test.gencot-manitems 
	$(IT) $(ABSINCL) used test.unit > test.gencot-extitems

%-dfltprops: %
	$(IT) file $* > $*-dfltprops

%.cogent: %.c
	$(GC) cfile $*.c

%-regression: types-%.cogent types-%-expected.cogent types-%.c-dfltprops types-%-expected.c-dfltprops
	-diff types-$*.cogent types-$*-expected.cogent
	-diff types-$*.c-dfltprops types-$*-expected.c-dfltprops

%-expect-current: types-%.cogent types-%.c-dfltprops
	cp types-$*.cogent types-$*-expected.cogent
	cp types-$*.c-dfltprops types-$*-expected.c-dfltprops

%-clean:
	-rm -f types-$*.cogent types-$*.o types-$*.c-dfltprops types-$*.c-itemprops

test.unit-itemprops: itemprops
	cp test.ext-itemprops test.unit-itemprops
	@for f in $(foreach TST,$(TESTS),types-$(TST).c-itemprops); do \
	  $(IT) merge $$f test.unit-itemprops > iprops; \
	  mv iprops test.unit-itemprops; \
	done

test.unit: 
	@for f in $(foreach TST,$(TESTS),types-$(TST).c); do \
	  echo $$f >> test.unit; \
	done
	@echo extrefs.c >> test.unit
	@cat test.unit

unit: test.unit test.unit-itemprops test.gencot-manitems
	$(GC) $(ABSINCL) unit test.unit types-parmod.json
