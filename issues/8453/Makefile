# SPDX-License-Identifier: Apache-2.0

FILE = main
TARGET ?= f

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

f: $(FILE)_contracts.goto results_smt

results_smt: $(FILE)_contracts.goto
	cbmc --bitwuzla $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc $(TARGET)_harness --enforce-contract $(TARGET) --apply-loop-contracts $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $^

clean:
	rm -f *.goto
