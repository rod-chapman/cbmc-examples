# Modularity

This directory contains example of modular reasoning using contracts in CBMC.

## Inc() and Inc2()

The first example (in files `q.h` and `q.c`) shows a functions inc2() that calls
another function inc(), which is specified with contracts in `p.h`

This shows that we can verify properties of inc2() without access to the full
definition and body inc(), which is not supplied.
