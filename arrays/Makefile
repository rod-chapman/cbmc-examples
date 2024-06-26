FILE = ar
TARGET ?= arsum_blocks2

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

f1: $(FILE)_contracts.goto results
f2: $(FILE)_contracts.goto results
f3: $(FILE)_contracts.goto results
arsum_blocks1: $(FILE)_contracts.goto results
arsum_blocks2: $(FILE)_contracts.goto results
arsum_bytes1: $(FILE)_contracts.goto results
arsum_bytes2: $(FILE)_contracts.goto results
assign_st1: $(FILE)_contracts.goto results_sat
assign_st2: $(FILE)_contracts.goto results_smt
assign_st3: $(FILE)_contracts.goto results_smt
init_st: $(FILE)_contracts.goto results_smt
zero_slice: $(FILE)_contracts.goto results_smt
constant_time_equals_strict: $(FILE)_contracts.goto results_smt
constant_time_equals_total: $(FILE)_contracts.goto results_smt
ctcc: $(FILE)_contracts.goto results_smt
ctunpad: $(FILE)_contracts.goto results_smt

ifeq ($(strip $(TARGET)),constant_time_equals_total)
  CALLS = --replace-call-with-contract constant_time_equals_strict
else ifeq ($(strip $(TARGET)),ctunpad)
  CALLS = --replace-call-with-contract ctcc
else
  CALLS =
endif


results: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --external-sat-solver cadical $<

results_sat: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --external-sat-solver cadical $<

results_smt: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --smt2 $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $(CALLS) $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto
