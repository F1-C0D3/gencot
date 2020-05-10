GC=../../bin/gencot
IT=../../bin/items

TESTS = prim enum struct union array func parmod pointer names const extrefs
UNIT = externs exttypes dvdtypes
ABSINCL = -I/home/teege/work/projekte/code/HoBit/devel/gencot/test/types-regression
AUNIT = unit-extitems ext-dfltprops

compile: $(foreach TST,$(TESTS),types-$(TST).o)

cogent: $(foreach TST,$(TESTS),types-$(TST).cogent) unit

dfltprops: $(foreach TST,$(TESTS),types-$(TST).c-dfltprops) test.ext-dfltprops

itemprops: $(foreach TST,$(TESTS),types-$(TST).c-itemprops) test.ext-itemprops

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -f test.unit test.cogent $(foreach U,$(UNIT),test-$(U).cogent)
	-rm -f test.unit-extitems test.ext-dfltprops test.ext-itemprops test.unit-itemprops

types-pointer.c-itemprops: types-pointer.c-manprops types-pointer.c-dfltprops types-parmod.json-itemprops
	@$(IT) mergeto types-pointer.c-dfltprops types-parmod.json-itemprops > types-pointer.c-hprops
	@$(IT) merge common.types-manprops types-pointer.c-hprops > types-pointer.c-h2props
	@$(IT) merge types-pointer.c-h2props types-pointer.c-manprops > types-pointer.c-itemprops
	@rm types-pointer.c-hprops types-pointer.c-h2props

types-const.c-itemprops: types-const.c-manprops types-const.c-dfltprops types-parmod.json-itemprops
	@$(IT) mergeto types-const.c-dfltprops types-parmod.json-itemprops > types-const.c-hprops
	@$(IT) merge common.types-manprops types-const.c-hprops > types-const.c-h2props
	@$(IT) merge types-const.c-h2props types-const.c-manprops > types-const.c-itemprops
	@rm types-const.c-hprops types-const.c-h2props

%.ext-itemprops: %.ext-dfltprops %.ext-manprops types-parmod.json-itemprops types-parmod.json-omitprops common.types-manprops
	@$(IT) mergeto $*.ext-dfltprops types-parmod.json-itemprops > $*.ext-hprops
	@$(IT) omitfrom $*.ext-hprops types-parmod.json-omitprops > $*.ext-h2props
	@$(IT) mergeto $*.ext-h2props $*.ext-manprops > $*.ext-hprops
	@$(IT) merge common.types-manprops $*.ext-hprops > $*.ext-itemprops
	@rm $*.ext-hprops $*.ext-h2props

%.c-itemprops: %.c-dfltprops types-parmod.json-itemprops types-parmod.json-omitprops common.types-manprops
	@$(IT) mergeto $*.c-dfltprops types-parmod.json-itemprops > $*.c-hprops
	@$(IT) omitfrom $*.c-hprops types-parmod.json-omitprops > $*.c-h2props
	@$(IT) merge common.types-manprops $*.c-h2props > $*.c-itemprops
	@rm $*.c-hprops $*.c-h2props

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

test.ext-dfltprops: test.unit test.unit-manitems
	@$(IT) $(ABSINCL) -u test unit > test.ext-dfltprops

test.unit-extitems: test.unit test.unit-manitems 
	@$(IT) $(ABSINCL) -u test used > test.unit-extitems

%.c-dfltprops: %.c
	@$(IT) $(ABSINCL) file $*.c > $*.c-dfltprops

%.cogent: %.c %.c-itemprops
	@$(GC) $(ABSINCL) cfile $*.c

%-regression: types-%.cogent types-%-expected.cogent types-%.c-dfltprops types-%-expected.c-dfltprops
	-diff types-$*.cogent types-$*-expected.cogent
	-diff types-$*.c-dfltprops types-$*-expected.c-dfltprops

%-expect-current: types-%.cogent types-%.c-dfltprops
	cp types-$*.cogent types-$*-expected.cogent
	cp types-$*.c-dfltprops types-$*-expected.c-dfltprops

%-clean:
	-rm -f types-$*.cogent types-$*.o types-$*.c-dfltprops types-$*.c-itemprops

test.unit-itemprops: itemprops
	@cp test.ext-itemprops test.unit-itemprops
	@for f in $(foreach TST,$(TESTS),types-$(TST).c-itemprops); do \
	  $(IT) merge $$f test.unit-itemprops > iprops; \
	  mv iprops test.unit-itemprops; \
	done

test.unit: 
	@for f in $(foreach TST,$(TESTS),types-$(TST).c); do \
	  echo $$f >> test.unit; \
	done
	@cat test.unit

unit: test.unit test.unit-itemprops test.unit-manitems
	@$(GC) $(ABSINCL) -u test unit
