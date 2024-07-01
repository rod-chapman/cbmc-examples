# SPDX-License-Identifier: Apache-2.0

FILE = main
TARGET ?= main

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

main: $(FILE)_contracts.goto results_smt

results_smt: $(FILE)_contracts.goto
	cbmc $(CHECKS) --verbosity 6 --smt2 $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc main --apply-loop-contracts $< $@

$(FILE).goto: $(FILE).c
	goto-cc -o $@ $^

clean:
	rm -f *.goto
