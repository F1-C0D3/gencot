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

parmod-external.items: parmod.unit
	@$(IT) $(ABSINCL) -u parmod used

%-close.json: %.c parmod-external.items
	@$(PM) $(ABSINCL) -u parmod close $*.c > $*-close.json

%.json: %.c parmod-external.items
	@$(PM) $(ABSINCL) -u parmod file $*.c > $*.json

parmod-externs.json: close-json parmod.unit
	@echo '[]' > parmod-externs.tmp
	@for f in $(foreach TST,$(TESTS),parmod-$(TST)-close.json); do \
	  $(PM) mergin parmod-externs.tmp $$f; \
	done
	@$(PM) $(ABSINCL) -u parmod unit parmod-externs.tmp > parmod-externs.json
	@rm parmod-externs.tmp

unit-regression: parmod-externs.json parmod-externs-expected.json
	-diff parmod-externs.json parmod-externs-expected.json

unit-expect-current: parmod-externs.json
	cp parmod-externs.json parmod-externs-expected.json

%-regression: parmod-%.json parmod-%-expected.json parmod-%-close.json parmod-%-close-expected.json
	-diff parmod-$*.json parmod-$*-expected.json
	-diff parmod-$*-close.json parmod-$*-close-expected.json

%-expect-current:  parmod-%.json parmod-%-close.json
	cp parmod-$*.json parmod-$*-expected.json
	cp parmod-$*-close.json parmod-$*-close-expected.json

%-clean:
	-rm -f parmod-$*.json parmod-$*-close.json parmod-$*.o 
	-rm -f parmod.unit parmod-external.items parmod-externs.json

