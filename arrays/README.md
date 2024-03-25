# Arrays

This directory contains example of how array types and operations thereon can
be handled and verified by CBMC using contracts and modular verification.

## Reproducing the results

Assuming you have CBMC 5.95.1 or better installed, the Makefile here
runs the proofs for a particular function by specifying that function's name
on the command line as the value of the TARGET environment variable. e.g.

```
make TARGET=assign_st3
```

The functions declared in ar.h and ar.c are as follows:

## Array Initialization - functions f1 - f3

These functions illustrate how to initialize an array element-by-element
but using different function signatures.

In f1, the formal parameter is a "pointer to element" type.

```
void f1 (uint32_t *s)
__CPROVER_requires(__CPROVER_is_fresh(s, C * sizeof(uint32_t)))
__CPROVER_assigns(__CPROVER_object_upto(s, C * sizeof(uint32_t)));
```

In f2, the formal parameter is a "static" array type.

```
void f2 (uint32_t s[static C])
__CPROVER_requires(__CPROVER_is_fresh(s, C * sizeof(uint32_t)))
__CPROVER_assigns(__CPROVER_object_whole(s));
```

In f3, the formal parameter is the name of a typedef of an array type.

```
typedef uint32_t st[C];
void f3 (st s)
__CPROVER_requires(__CPROVER_is_fresh(s, sizeof(st)))
__CPROVER_assigns(__CPROVER_object_whole(s));
```

## Array summation by blocks

function arsum_blocks1() forms the 32-bit sum of an array of bytes,
summing 4 bytes at a time, using array indexing

```
#define BLOCK_SIZE 4

// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks1(const uint8_t *data, size_t num_blocks)
__CPROVER_requires(num_blocks >= 1)
__CPROVER_requires(num_blocks <= LONG_MAX / BLOCK_SIZE)
__CPROVER_requires(__CPROVER_is_fresh(data, num_blocks * BLOCK_SIZE));
```

function arsum_blocks1() forms the 32-bit sum of an array of bytes,
summing 4 bytes at a time, but this time using pointer arithmetic:

```
// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks2(const uint8_t *data, size_t num_blocks)
__CPROVER_requires(num_blocks >= 1)
__CPROVER_requires(num_blocks <= LONG_MAX / BLOCK_SIZE)
__CPROVER_requires(__CPROVER_is_fresh(data, num_blocks * BLOCK_SIZE));
```

## Array summation by bytes

arsum_bytes1() forms the sum of bytes of an array, using array indexing

```
// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes1(const uint8_t *data, size_t num_bytes)
__CPROVER_requires(num_bytes >= 1)
__CPROVER_requires(num_bytes <= LONG_MAX)
__CPROVER_requires(__CPROVER_is_fresh(data, num_bytes));
```

arsum_bytes2() does the same, but uses pointer-arithmetic internally:

```
// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes2(const uint8_t *data, size_t num_bytes)
__CPROVER_requires(num_bytes >= 1)
__CPROVER_requires(num_bytes <= LONG_MAX)
__CPROVER_requires(__CPROVER_is_fresh(data, num_bytes));
```

## Array assignment

These functions "wrap" assignment of a whole array from source to destination,
but declared and implemented different ways. All three functions have the
same declaration, with an "ensures" clause that shows correctness of the
assignment:

```
// Array assignment - an abstraction of array assignment
// with contracts that show all values copied.
void assign_stX (st dst, const st src)
__CPROVER_requires(__CPROVER_is_fresh(dst, sizeof(st)))
__CPROVER_requires(__CPROVER_is_fresh(src, sizeof(st)))
__CPROVER_assigns(__CPROVER_object_whole(dst))
__CPROVER_ensures(__CPROVER_forall { size_t i; (0 <= i && i < C) ==> dst[i] == src[i] });
```

assign_st1() is implemented by copying array elements one at a time.

assign_st2() is implemented using a simple "for" loop.

assign_st3() is implemented by a direct call to "memcpy()"
