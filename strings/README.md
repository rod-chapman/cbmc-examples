# Strings

This directory contains example of how character strings can
be handled and verified by CBMC using contracts and modular verification.

## Reproducing the results

Assuming you have CBMC 5.95.1 or better installed, the Makefile here
runs the proofs for a particular function by specifying that function's name
on the command line as the value of the TARGET environment variable. e.g.

```
make TARGET=tl1
```

The functions declared in str.h and str.c are as follows:

## tl1 - String to Lower Case

Applies tolower() (from C's ctype.h library) to each
character of the given string of the given length.
Proves partial correctness using a quantified post-condition,
also using tolower() as an uninterpreted function.
