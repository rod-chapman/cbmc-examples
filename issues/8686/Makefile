FILE = q
TARGET ?= mld_polyveck_caddq

all: clean $(TARGET)

$(TARGET): $(FILE)_contracts.goto results

b.smt2: $(FILE)_contracts.goto
	cbmc --bitwuzla --outfile $@ --bitwuzla $<

results: b.smt2
	bitwuzla $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) --replace-call-with-contract caddq $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto *.smt2
