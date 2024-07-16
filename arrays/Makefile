FILE = ar
TARGET ?= arsum_blocks2

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

# Functions that prove best with Cadical
f1: $(FILE)_contracts.goto results_cadical
f2: $(FILE)_contracts.goto results_cadical
f3: $(FILE)_contracts.goto results_cadical
arsum_blocks1: $(FILE)_contracts.goto results_cadical
arsum_blocks2: $(FILE)_contracts.goto results_cadical
arsum_bytes1: $(FILE)_contracts.goto results_cadical
arsum_bytes2: $(FILE)_contracts.goto results_cadical
assign_st1: $(FILE)_contracts.goto results_cadical

# Functions that prove best with Z3
assign_st2: $(FILE)_contracts.goto results_z3
assign_st3: $(FILE)_contracts.goto results_z3
init_st: $(FILE)_contracts.goto results_z3
zero_slice: $(FILE)_contracts.goto results_z3

# Functions that prove best with Bitwuzla
constant_time_equals_strict: $(FILE)_contracts.goto results_bitwuzla
constant_time_equals_total: $(FILE)_contracts.goto results_bitwuzla
ctcc: $(FILE)_contracts.goto results_bitwuzla
ctunpad: $(FILE)_contracts.goto results_bitwuzla


ifeq ($(strip $(TARGET)),constant_time_equals_total)
  CALLS = --replace-call-with-contract constant_time_equals_strict
else ifeq ($(strip $(TARGET)),ctunpad)
  CALLS = --replace-call-with-contract ctcc
else
  CALLS =
endif


results_cadical: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --external-sat-solver cadical $<

results_z3: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --smt2 $<

results_bitwuzla: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --bitwuzla $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $(CALLS) $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto
