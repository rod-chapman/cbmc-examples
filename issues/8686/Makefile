FILE = q
TARGET ?= mld_polyveck_caddq

CHECKS=--bounds-check --pointer-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

$(TARGET): $(FILE)_contracts.goto results

b.smt2: $(FILE)_contracts.goto
	cbmc $(CHECKS) --bitwuzla --outfile $@ --bitwuzla $<

results: b.smt2
	bitwuzla $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) --replace-call-with-contract caddq $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto *.smt2
