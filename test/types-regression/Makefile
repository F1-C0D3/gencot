GC=../../bin/gencot
PM=../../bin/parmod
IT=../../bin/items

TESTS = union 
# prim enum struct union array func parmod pointer names const
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
	-rm -f types-parmod.json-itemprops types-parmod.json-omitprops
	-rm -f test.unit-extitems test.ext-dfltprops test.ext-itemprops test.unit-itemprops

types-parmod.json-itemprops types-parmod.json-omitprops: types-parmod.json
	@$(PM) out types-parmod.json

types-pointer.c-itemprops: types-pointer.c-manprops types-pointer.c-dfltprops types-parmod.json-itemprops
	@$(IT) mergeto types-pointer.c-dfltprops types-parmod.json-itemprops > types-pointer.c-hprops
	@$(IT) merge common.types-manprops types-pointer.c-hprops > types-pointer.c-h2props
	@$(IT) merge types-pointer.c-h2props types-pointer.c-manprops > types-pointer.c-itemprops
	@rm types-pointer.c-hprops types-pointer.c-h2props

%-itemprops: %-dfltprops types-parmod.json-itemprops types-parmod.json-omitprops common.types-manprops
	@$(IT) mergeto $*-dfltprops types-parmod.json-itemprops > $*-hprops
	@$(IT) omitfrom $*-hprops types-parmod.json-omitprops > $*-h2props
	@$(IT) merge common.types-manprops $*-h2props > $*-itemprops
	@rm $*-hprops $*-h2props

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
	@$(IT) $(ABSINCL) unit test.unit > test.ext-dfltprops

test.unit-extitems: test.unit test.unit-manitems 
	@$(IT) $(ABSINCL) used test.unit > test.unit-extitems

%-dfltprops: %
	@$(IT) file $* > $*-dfltprops

%.cogent: %.c %.c-itemprops
	@$(GC) cfile $*.c

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
	@echo extrefs.c >> test.unit
	@cat test.unit

unit: test.unit test.unit-itemprops test.unit-manitems
	@$(GC) $(ABSINCL) unit test.unit
