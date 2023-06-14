FILE = ar
TARGET ?= arsum_bytes1

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

f1: $(FILE)_contracts.goto results
f2: $(FILE)_contracts.goto results
f3: $(FILE)_contracts.goto results
arsum_blocks: $(FILE)_contracts.goto results
arsum_bytes1: $(FILE)_contracts.goto results
arsum_bytes2: $(FILE)_contracts.goto results


results: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --external-sat-solver cadical $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument $(CHECKS) --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto
