#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <limits.h>

#define C 8

#ifdef CBMC
#else
#define __CPROVER_assigns(...)
#define __CPROVER_decreases(...)
#define __CPROVER_assert(...)
#define __CPROVER_requires(...)
#define __CPROVER_ensures(...)
#define __CPROVER_loop_invariant(...)
#endif

void f1 (uint32_t *s)
__CPROVER_requires(__CPROVER_is_fresh(s, C * sizeof(uint32_t)))
__CPROVER_assigns(__CPROVER_object_upto(s, C * sizeof(uint32_t)));

void f2 (uint32_t s[static C])
__CPROVER_requires(__CPROVER_is_fresh(s, C * sizeof(uint32_t)))
__CPROVER_assigns(__CPROVER_object_whole(s));

typedef uint32_t st[C];
void f3 (st s)
__CPROVER_requires(__CPROVER_is_fresh(s, sizeof(st)))
__CPROVER_assigns(__CPROVER_object_whole(s));

#define BLOCK_SIZE 4

// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks1(const uint8_t *data, size_t num_blocks)
__CPROVER_requires(num_blocks >= 1)
__CPROVER_requires(num_blocks <= LONG_MAX / BLOCK_SIZE)
__CPROVER_requires(__CPROVER_is_fresh(data, num_blocks * BLOCK_SIZE));

// 32-bit unsigned sum of data[0 .. num_blocks * BLOCK_SIZE - 1]
uint32_t arsum_blocks2(const uint8_t *data, size_t num_blocks)
__CPROVER_requires(num_blocks >= 1)
__CPROVER_requires(num_blocks <= LONG_MAX / BLOCK_SIZE)
__CPROVER_requires(__CPROVER_is_fresh(data, num_blocks * BLOCK_SIZE));

// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes1(const uint8_t *data, size_t num_bytes)
__CPROVER_requires(num_bytes >= 1)
__CPROVER_requires(num_bytes <= LONG_MAX)
__CPROVER_requires(__CPROVER_is_fresh(data, num_bytes));

// 32-bit unsigned sum of data[0 .. num_bytes - 1]
uint32_t arsum_bytes2(const uint8_t *data, size_t num_bytes)
__CPROVER_requires(num_bytes >= 1)
__CPROVER_requires(num_bytes <= LONG_MAX)
__CPROVER_requires(__CPROVER_is_fresh(data, num_bytes));

// Array assignment - an abstraction of array assignment
// with contracts that show all values copied.
void assign_st1 (st dst, const st src)
__CPROVER_requires(__CPROVER_is_fresh(dst, sizeof(st)))
__CPROVER_requires(__CPROVER_is_fresh(src, sizeof(st)))
__CPROVER_assigns(__CPROVER_object_whole(dst))
__CPROVER_ensures(__CPROVER_forall { size_t i; (0 <= i && i < C) ==> dst[i] == src[i] });

void assign_st2 (st dst, const st src)
__CPROVER_requires(__CPROVER_is_fresh(dst, sizeof(st)))
__CPROVER_requires(__CPROVER_is_fresh(src, sizeof(st)))
__CPROVER_assigns(__CPROVER_object_whole(dst))
__CPROVER_ensures(__CPROVER_forall { size_t i; (0 <= i && i < C) ==> dst[i] == src[i] });

void assign_st3 (st dst, const st src)
__CPROVER_requires(__CPROVER_is_fresh(dst, sizeof(st)))
__CPROVER_requires(__CPROVER_is_fresh(src, sizeof(st)))
__CPROVER_assigns(__CPROVER_object_whole(dst))
__CPROVER_ensures(__CPROVER_forall { size_t i; (0 <= i && i < C) ==> dst[i] == src[i] });


/* Returns true if a and b are equal. Execution time may depend on len */
/* but not on the value of the data denoted by a or b                  */
/* Note that if len == 0, then returns true                            */
bool constant_time_equals_strict(const uint8_t* const a,
                                 const uint8_t* const b,
                                 const uint32_t len)
__CPROVER_requires(a != NULL && __CPROVER_is_fresh(a, len))
__CPROVER_requires(b != NULL && __CPROVER_is_fresh(b, len))
__CPROVER_ensures(__CPROVER_return_value == __CPROVER_forall { size_t i; (i >= 0 && i < len) ==> (a[i] == b[i]) });

/* Returns true if a and b are equal. Execution time may depend on len */
/* but not on the value of the data denoted by a or b                  */
/* If either of a or b is NULL, then returns false                     */
bool constant_time_equals_total(const uint8_t* const a,
                                const uint8_t* const b,
                                const uint32_t len)
__CPROVER_requires(__CPROVER_is_fresh(a, len))
__CPROVER_requires(__CPROVER_is_fresh(b, len))
__CPROVER_ensures(__CPROVER_return_value == (a != NULL && b != NULL) ? __CPROVER_forall { size_t i; (i >= 0 && i < len) ==> (a[i] == b[i]) } : false );

/* Constant Time Condition Copy */
int ctcc(uint8_t* dst, const uint8_t* src, uint32_t len, uint8_t dont)
__CPROVER_requires(dst != NULL && __CPROVER_is_fresh(dst, len))
__CPROVER_requires(src != NULL && __CPROVER_is_fresh(src, len))
__CPROVER_assigns(__CPROVER_object_whole(dst))
__CPROVER_ensures(__CPROVER_return_value == 0)
__CPROVER_ensures(dont > 0 ?
                  (__CPROVER_forall { size_t i; (i >= 0 && i < len) ==> (dst [i] == __CPROVER_old(dst)[i]) } )
                  :
                  (__CPROVER_forall { size_t i; (i >= 0 && i < len) ==> (dst [i] == src [i]) } ));
