FILE=mod3329

all: $(TARGET)

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check


$(TARGET): $(FILE)_contracts.goto
	-cbmc --verbosity 6 $(CHECKS) --external-sat-solver cadical $<
	rm -f *.goto

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument $(CHECKS) --dfcc $(TARGET)_harness --apply-loop-contracts --enforce-contract $(TARGET) $< $@

$(FILE).goto: $(FILE).c
	goto-cc --function $(TARGET)_harness -DCBMC -o $@ $<

testmod: testmod.c mod3329.h mod3329.c
	gcc -S -Os mod3329.c
	mv mod3329.s mod3329Os.s
	gcc -S -O2 mod3329.c
	mv mod3329.s mod3329O2.s
	gcc -c mod3329.c
	gcc -c testmod.c
	gcc -o $@ testmod.o mod3329.o

clean:
	rm -f *.goto
