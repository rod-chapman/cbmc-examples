# Arrays

This directory contains example of how array types and operations thereon can
be handled and verified by CBMC using contracts and modular verification.

## Reproducing the results

Assuming you have CBMC 6.4.1 or better installed, the Makefile here
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
void f1(uint32_t *s)
__contract__(
  requires(memory_no_alias(s, C * sizeof(uint32_t)))
  assigns(memory_slice(s, C * sizeof(uint32_t)))
);
```

In f2, the formal parameter is a "static" array type.

```
void f2(uint32_t s[static C])
__contract__(
  requires(memory_no_alias(s, C * sizeof(uint32_t)))
  assigns(object_whole(s))
);
```

In f3, the formal parameter is the name of a typedef of an array type.

```
typedef uint32_t st[C];
void f3(st s)
__contract__(
  requires(memory_no_alias(s, sizeof(st)))
  assigns(object_whole(s))
);
```

## Array summation by blocks

function arsum_blocks1() forms the 32-bit sum of an array of bytes,
summing 4 bytes at a time, using array indexing

```
#define BLOCK_SIZE 4

// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks1(const uint8_t *data, size_t num_blocks)
__contract__(
  requires(num_blocks >= 1)
  requires(num_blocks <= LONG_MAX / BLOCK_SIZE)
  requires(memory_no_alias(data, num_blocks *BLOCK_SIZE))
);
```

function arsum_blocks1() forms the 32-bit sum of an array of bytes,
summing 4 bytes at a time, but this time using pointer arithmetic:

```
// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks2(const uint8_t *data, size_t num_blocks)
__contract__(
  requires(num_blocks >= 1) requires( num_blocks <= LONG_MAX / BLOCK_SIZE)
  requires(memory_no_alias(data, num_blocks *BLOCK_SIZE))
);
```

## Array summation by bytes

arsum_bytes1() forms the sum of bytes of an array, using array indexing

```
// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes1(const uint8_t *data, size_t num_bytes)
__contract__(
  requires(num_bytes >= 1)
  requires(num_bytes <= LONG_MAX)
  requires(memory_no_alias(data, num_bytes))
);
```

arsum_bytes2() does the same, but uses pointer-arithmetic internally:

```
// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes2(const uint8_t *data, size_t num_bytes)
__contract__(
  requires(num_bytes >= 1)
  requires(num_bytes <= LONG_MAX)
  requires(memory_no_alias(data, num_bytes))
);
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
__contract__(
  requires(memory_no_alias(dst, sizeof(st)))
  requires(memory_no_alias(src, sizeof(st)))
  assigns(object_whole(dst))
  ensures(forall (i, 0, C, dst[i] == src[i]))
);
```

assign_st1() is implemented by copying array elements one at a time.

assign_st2() is implemented using a simple "for" loop.

assign_st3() is implemented by a direct call to "memcpy()"

## Array initialization

These functions demonatrate initialization of an array so
that every element has some constant value.

```
void init_st(st dst)
__contract__(
  requires(memory_no_alias(dst, sizeof(st)))
  assigns(object_whole(dst))
  ensures(forall(k, 0, C, dst[k] == 0))
);
```

and

```
void zero_array_correct(uint8_t *dst, unsigned len)
__contract__(
  requires(memory_no_alias(dst, len))
  assigns(object_whole(dst))
  ensures(forall(k, 0, len, dst[k] == 0))
);
```

## Constant time array equality

These functions demonstrate proof of array equality,
but implemented in the constant-time style. The specification looks
like this:

```
bool constant_time_equals_strict(const uint8_t *const a, const uint8_t *const b,
                                 const uint32_t len)
__contract__(
  requires(memory_no_alias(a, len))
  requires(memory_no_alias(b, len))
  ensures(return_value == forall(k, 0, len, a[k] == b[k]))
);
```

## Constant time conditional array copy

This function copies one array onto another if a flag is set, but
in constant time.

```
int ctcc(uint8_t *dst, const uint8_t *src, uint32_t len, uint8_t dont)
__contract__(
  requires(memory_no_alias(dst, len))
  requires(memory_no_alias(src, len))
  assigns(object_whole(dst))
  ensures(return_value == 0)
  ensures(dont > 0 ? (forall(i, 0, len, dst[i] == old(dst)[i]))
                   : (forall(i, 0, len, dst[i] == src[i])))
);
```
