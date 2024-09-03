FILE=crypto

all: $(TARGET)

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check


$(TARGET): $(FILE)_contracts.goto kissat

sat: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) $<

z3: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --smt2 $<

bitwuzla: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --bitwuzla $<

kissat: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --external-sat-solver kissat $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument $(CHECKS) --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

testmod: testmod.c crypto.h crypto.c
	gcc -S -Os crypto.c
	mv crypto.s cryptoOs.s
	gcc -S -O2 crypto.c
	mv crypto.s cryptoO2.s
	gcc -c crypto.c
	gcc -c testmod.c
	gcc -o $@ testmod.o crypto.o

clean:
	rm -f *.goto
