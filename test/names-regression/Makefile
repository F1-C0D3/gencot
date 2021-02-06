# invoke as 
#   make DFLT=T ...
# to use default mapping for empty prefix instead of explicit mapping

GC=../../bin/gencot
IT=../../bin/items

BASE = names
TESTS = test
UNIT = externs exttypes dvdtypes
UFILES = $(foreach U,$(UNIT),all-$(U).cogent)

compile: $(foreach TST,$(TESTS),$(BASE)-$(TST).o)

cogent: $(foreach TST,$(TESTS),$(BASE)-$(TST).cogent) $(UFILES)

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -r -f comments names-test-incl.cogent
	-rm -f all.unit all.cogent $(UFILES) all-external.items common.gencot-namap

common.gencot-namap: prepared.gencot-namap
	@cp prepared.gencot-namap common.gencot-namap
ifndef DFLT
	@echo "cogent_" >> common.gencot-namap
endif

all-external.items: all.unit
	@$(IT) used

unit-regression: $(UFILES) $(foreach U,$(UNIT),all-$(U)-expected.cogent)
	-@for u in $(UNIT); do \
	  echo "diff all-$$u.cogent all-$$u-expected.cogent"; \
	  diff all-$$u.cogent all-$$u-expected.cogent; \
	done

unit-expect-current: $(UFILES)
	@for u in $(UNIT); do \
	  echo "cp all-$$u.cogent all-$$u-expected.cogent"; \
	  cp all-$$u.cogent all-$$u-expected.cogent; \
	done

%.cogent: %.c %.h all-external.items common.gencot-namap
	@$(GC) hfile $*.h
	@$(GC) cfile $*.c

%-regression: $(BASE)-%.cogent $(BASE)-%-expected.cogent
	-diff $(BASE)-$*.cogent $(BASE)-$*-expected.cogent
	-diff $(BASE)-$*-entry.ac $(BASE)-$*-entry-expected.ac

%-expect-current: $(BASE)-%.cogent
	cp $(BASE)-$*.cogent $(BASE)-$*-expected.cogent
	cp $(BASE)-$*-entry.ac $(BASE)-$*-entry-expected.ac

%-clean:
	-rm -f $(BASE)-$*.cogent $(BASE)-$*.o $(BASE)-$*-entry.ac

all.unit: 
	@for f in $(foreach TST,$(TESTS),$(BASE)-$(TST).c); do \
	  echo $$f >> all.unit; \
	done
	@cat all.unit

$(UFILES): all.unit all-external.items common.gencot-namap
	@$(GC) unit
