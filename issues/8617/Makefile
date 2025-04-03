all: final.goto

# This sequence of commands is copied from what the CBMC starter kit does
# when run with VERBOSE=1
final.goto: poly.h polyvec.h polyvec.c polyveck_decompose_harness.c
	goto-cc  -Wall -Werror --native-compiler clang -I. -DCBMC=1 -DCBMC_OBJECT_BITS=8 -DCBMC_MAX_OBJECT_SIZE="(SIZE_MAX>>(CBMC_OBJECT_BITS+1))" -DMLDSA_MODE=2 -Dstatic= polyveck_decompose_harness.c -o proof0100.goto
	goto-cc  -Wall -Werror --native-compiler clang -I. -DCBMC=1 -DCBMC_OBJECT_BITS=8 -DCBMC_MAX_OBJECT_SIZE="(SIZE_MAX>>(CBMC_OBJECT_BITS+1))" -DMLDSA_MODE=2 -Dstatic= polyvec.c -o project0100.goto
	goto-instrument project0100.goto project0200.goto
	goto-cc --function harness proof0100.goto project0200.goto -Wall -Werror -o polyveck_decompose_harness0100.goto
	goto-instrument --remove-function-pointers polyveck_decompose_harness0100.goto polyveck_decompose_harness0200.goto
	cp polyveck_decompose_harness0200.goto polyveck_decompose_harness0300.goto
	goto-instrument --add-library polyveck_decompose_harness0300.goto polyveck_decompose_harness0400.goto
	goto-instrument polyveck_decompose_harness0400.goto polyveck_decompose_harness0500.goto
	goto-instrument --dfcc harness --enforce-contract polyveck_decompose --replace-call-with-contract poly_decompose --apply-loop-contracts polyveck_decompose_harness0500.goto polyveck_decompose_harness0600.goto
	goto-instrument  --slice-global-inits polyveck_decompose_harness0600.goto polyveck_decompose_harness0700.goto
	goto-instrument  --drop-unused-functions polyveck_decompose_harness0700.goto polyveck_decompose_harness0800.goto
	cp polyveck_decompose_harness0800.goto final.goto

# Warning - this genereates about 1.5GB z.smt2 file using CBMC 6.5.0
# and takes about 30 minutes to run on an Apple MacBook Pro M1
smt: final.goto
	cbmc --smt2 --outfile z.smt2 --z3 final.goto

# And this does not terminate in a reasonble time
results: final.goto
	cbmc --smt2 final.goto
