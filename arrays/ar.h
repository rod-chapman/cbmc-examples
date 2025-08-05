#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "../common/cbmc.h"
#define C 8

void f1(uint32_t *s)
__contract__(
  requires(memory_no_alias(s, C * sizeof(uint32_t)))
  assigns(memory_slice(s, C * sizeof(uint32_t)))
);

void f2(uint32_t s[static C])
__contract__(
  requires(memory_no_alias(s, C * sizeof(uint32_t)))
  assigns(object_whole(s))
);

typedef uint32_t st[C];
void f3(st s)
__contract__(
  requires(memory_no_alias(s, sizeof(st)))
  assigns(object_whole(s))
);

#define BLOCK_SIZE 4

// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks1(const uint8_t *data, size_t num_blocks)
__contract__(
  requires(num_blocks >= 1)
  requires(num_blocks <= LONG_MAX / BLOCK_SIZE)
  requires(memory_no_alias(data, num_blocks *BLOCK_SIZE))
);

// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks2(const uint8_t *data, size_t num_blocks)
__contract__(
  requires(num_blocks >= 1) requires( num_blocks <= LONG_MAX / BLOCK_SIZE)
  requires(memory_no_alias(data, num_blocks *BLOCK_SIZE))
);

// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes1(const uint8_t *data, size_t num_bytes)
__contract__(
  requires(num_bytes >= 1)
  requires(num_bytes <= LONG_MAX)
  requires(memory_no_alias(data, num_bytes))
);

// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes2(const uint8_t *data, size_t num_bytes)
__contract__(
  requires(num_bytes >= 1)
  requires(num_bytes <= LONG_MAX)
  requires(memory_no_alias(data, num_bytes))
);

#define LEN_MAX 100
#define DATA_MIN -9
#define DATA_MAX 9
// 32-bit signed sum of signed 32-bit data[0 .. datalen - 1]
// with limits on the range of the data and length of the array
int32_t arsum_swords(const int32_t *data, const int32_t datalen)
__contract__(
  requires(datalen >= 1)
  requires(datalen <= LEN_MAX)
  requires(memory_no_alias(data, datalen * sizeof(int32_t)))
  requires(forall(k, 0, datalen, data[k] >= DATA_MIN && data[k] <= DATA_MAX))
  ensures(return_value >= LEN_MAX * DATA_MIN && return_value <= LEN_MAX * DATA_MAX)
);


// Array assignment - an abstraction of array assignment
// with contracts that show all values copied.
void assign_st1(st dst, const st src)
__contract__(
  requires(memory_no_alias(dst, sizeof(st)))
  requires(memory_no_alias(src, sizeof(st)))
  assigns(object_whole(dst))
  ensures(forall (i, 0, C, dst[i] == src[i]))
);


void assign_st2(st dst, const st src)
__contract__(
  requires(memory_no_alias(dst, sizeof(st)))
  requires(memory_no_alias(src, sizeof(st)))
  assigns(object_whole(dst))
  ensures(forall(i, 0, C, dst[i] == src[i]))
);

void assign_st3(st dst, const st src)
__contract__(
  requires(memory_no_alias(dst, sizeof(st)))
  requires(memory_no_alias(src, sizeof(st)))
  assigns(object_whole(dst))
  ensures(forall(i, 0, C, dst[i] == src[i]))
);

void init_st(st dst)
__contract__(
  requires(memory_no_alias(dst, sizeof(st)))
  assigns(object_whole(dst))
  ensures(forall(k, 0, C, dst[k] == 0))
);

void zero_slice(uint8_t *dst, size_t len)
__contract__(
  requires(memory_no_alias(dst, len))
  assigns(memory_slice(dst, len))
  ensures(forall(k, 0, len, dst[k] == 0))
);

void zero_array_ts(uint8_t *dst, unsigned len)
__contract__(
  requires(memory_no_alias(dst, len))
  assigns(object_whole(dst))
);

void zero_array_correct(uint8_t *dst, unsigned len)
__contract__(
  requires(memory_no_alias(dst, len))
  assigns(object_whole(dst))
  ensures(forall(k, 0, len, dst[k] == 0))
);


/* Returns true if a and b are equal. Execution time may depend on len */
/* but not on the value of the data denoted by a or b                  */
/* Note that if len == 0, then returns true                            */
bool constant_time_equals_strict(const uint8_t *const a, const uint8_t *const b,
                                 const uint32_t len)
__contract__(
  requires(memory_no_alias(a, len))
  requires(memory_no_alias(b, len))
  ensures(return_value == forall(k, 0, len, a[k] == b[k]))
);

/* Returns true if a and b are equal. Execution time may depend on len */
/* but not on the value of the data denoted by a or b                  */
/* If either of a or b is NULL, then returns false                     */
bool constant_time_equals_total(const uint8_t *const a, const uint8_t *const b,
                                const uint32_t len)
__contract__(
  requires(memory_no_alias(a, len))
  requires(memory_no_alias(b, len))
  ensures(((a != NULL && b != NULL) &&
          return_value == constant_time_equals_strict(a, b, len)) ||
          ((a == NULL || b == NULL) && return_value == false))
);
// This form of postcondition using C's ternary ? : operator, but causes
// non-termination for Z3 and "unknown" from CVC5 with CBMC 6.0.0
// ensures(return_value == ((a != NULL && b != NULL) ?
// constant_time_equals_strict(a, b, len) : false) );



/* Constant Time Condition Copy */
int ctcc(uint8_t *dst, const uint8_t *src, uint32_t len, uint8_t dont)
__contract__(
  requires(memory_no_alias(dst, len))
  requires(memory_no_alias(src, len))
  assigns(object_whole(dst))
  ensures(return_value == 0)
  ensures(dont > 0 ? (forall(i, 0, len, dst[i] == old(dst)[i]))
                   : (forall(i, 0, len, dst[i] == src[i])))
);

/* Constant time conditional unpad */
int ctunpad(uint8_t *dst, const uint8_t *src, uint32_t srclen, uint32_t dstlen)
__contract__(
  requires(memory_no_alias(dst, dstlen))
  requires(memory_no_alias(src, srclen))
  requires(srclen > dstlen)
  requires(srclen - dstlen >= 3)
  assigns(object_whole(dst))
  ensures(return_value == 0)
);

/* New example/challenge for Kani */
#define LC 256

typedef int32_t vector[LC];
typedef vector matrix[LC];

void inc_vector(vector v)
__contract__(
  requires(memory_no_alias(v, sizeof(vector)))
  requires(forall(i0, 0, LC, v[i0] < INT32_MAX))
  assigns(object_whole(v))
  ensures(forall(i1, 0, LC, old(v)[i1] < INT32_MAX && v[i1] == old(v)[i1] + 1))
);

void inc_matrix(matrix m)
__contract__(
  requires(memory_no_alias(m, sizeof(matrix)))
  requires(forall(i, 0, LC,
                  forall(j, 0, LC, m[i][j] < INT32_MAX)))
  assigns(object_whole(m))
  ensures(forall(i, 0, LC,
                 forall(j, 0, LC, m[i][j] == old(m)[i][j] + 1)))
);
