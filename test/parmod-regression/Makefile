PM=../../bin/parmod
IT=../../bin/items

TESTS = test
ABSINCL = -I/home/teege/work/projekte/code/HoBit/devel/gencot/test/parmod-regression

compile: $(foreach TST,$(TESTS),parmod-$(TST).o)

json: $(foreach TST,$(TESTS),parmod-$(TST).json)

close-json: $(foreach TST,$(TESTS),parmod-$(TST)-close.json)

unit-json: parmod-externs.json

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current)

clean:  $(foreach TST,$(TESTS),$(TST)-clean)

parmod.unit:
	@for f in $(foreach TST,$(TESTS),parmod-$(TST).c); do \
	  echo $$f >> parmod.unit; \
	done

parmod.extitems: parmod.unit
	@$(IT) $(ABSINCL) used parmod.unit > parmod.extitems

%-close.json: %.c parmod.extitems
	@$(PM) $(ABSINCL) close $*.c parmod.extitems > $*-close.json

%.json: %.c parmod.extitems
	@$(PM) $(ABSINCL) file $*.c parmod.extitems > $*.json

parmod-externs.json: close-json parmod.unit
	@echo '[]' > parmod-externs.tmp
	@for f in $(foreach TST,$(TESTS),parmod-$(TST)-close.json); do \
	  $(PM) mergin parmod-externs.tmp $$f; \
	done
	@$(PM) $(ABSINCL) unit parmod.unit parmod-externs.tmp > parmod-externs.json
	@rm parmod-externs.tmp

unit-regression: parmod-externs.json parmod-externs-expected.json
	-diff parmod-externs.json parmod-externs-expected.json

unit-expect-current: parmod-externs.json
	cp parmod-externs.json parmod-externs-expected.json

%.json-itemprops %.json-omitprops: %.json
	@$(PM) out $*.json

%-regression: parmod-%.json parmod-%-expected.json parmod-%-close.json parmod-%-close-expected.json
	-diff parmod-$*.json parmod-$*-expected.json
	-diff parmod-$*-close.json parmod-$*-close-expected.json

%-expect-current:  parmod-%.json parmod-%-close.json
	cp parmod-$*.json parmod-$*-expected.json
	cp parmod-$*-close.json parmod-$*-close-expected.json

%-clean:
	-rm -f parmod-$*.json parmod-$*-close.json parmod-$*.o 
	-rm -f parmod.unit parmod.extitems parmod-externs.json
	-rm -f parmod-$*.json-itemprops parmod-$*.json-omitprops

