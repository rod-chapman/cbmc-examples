#include <stdint.h>
#include <stddef.h>

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
uint32_t arsum(const uint8_t *data, size_t num_blocks)
__CPROVER_requires(num_blocks >= 1)
__CPROVER_requires(__CPROVER_is_fresh(data, num_blocks * BLOCK_SIZE));
