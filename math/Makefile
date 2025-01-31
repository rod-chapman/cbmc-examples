TARGET=isqrt_correct
FILE=isqrt

all: $(TARGET)

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check


$(TARGET): $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --bitwuzla $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument $(CHECKS) --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $< $@

$(FILE).goto: $(FILE).c#
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto
