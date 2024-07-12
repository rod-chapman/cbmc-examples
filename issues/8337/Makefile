FILE = ar
TARGET ?= init_st

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

init_st: $(FILE)_contracts.goto results_smt

results_smt: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --smt2 $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto
