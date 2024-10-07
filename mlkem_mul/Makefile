FILE = mul
TARGET ?= mul32_proved

CC=clang

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET) testall

testall: mul.o testall.o
	$(CC) -o testall testall.o mul.o

mul.o: mul.c mul.h
	$(CC) -c -O3 mul.c

testall.o: mul.h testall.c
	$(CC) -c testall.c

# Functions that prove best with Z3
mul32: $(FILE)_contracts.goto results_z3
	echo "Done"

mul32_proved: $(FILE)_contracts.goto results_z3
	echo "Done"

results_z3: $(FILE)_contracts.goto
	cbmc --verbosity 6 $(CHECKS) --smt2 $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $(CALLS) $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

clean:
	rm -f *.goto *.o testall
