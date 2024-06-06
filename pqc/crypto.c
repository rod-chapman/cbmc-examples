#include "crypto.h"

#ifdef CBMC
#else
#define __CPROVER_assigns(...)
#define __CPROVER_decreases(...)
#define __CPROVER_assert(...)
#define __CPROVER_requires(...)
#define __CPROVER_ensures(...)
#define __CPROVER_loop_invariant(...)
#endif

uint16_t mod3329 (uint16_t a, uint16_t b)
{
    uint32_t r = (uint32_t) a * (uint32_t) b;
    r = r % Q;
    return (uint16_t) r;
}

const int64_t c = 1UL << 37;
const int64_t magic = c / Q;

uint16_t mod3329a (uint16_t a, uint16_t b)
{
    int32_t r1 = (int32_t) a * (int32_t) b;
    int64_t r2 = r1 * magic;
    int32_t r3 = (int32_t) (r2 / c);
    int32_t r4 = r3 * Q;
    int32_t r = r1 - r4;
    return (uint16_t) r;
}


uint16_t mod3329b (uint16_t a, uint16_t b)
__CPROVER_requires(a >= 0 && a < Q)
__CPROVER_requires(b >= 0 && b < Q)
{
    int32_t r1 = (int32_t) a * (int32_t) b;
    int64_t r2 = r1 * magic;
    int32_t r3 = (int32_t) (r2 / c);
    int32_t r4 = r3 * Q;
    int32_t r = r1 - r4;
    return (uint16_t) r;
}


uint16_t mod3329c (uint16_t a, uint16_t b)
__CPROVER_requires(a >= 0 && a < Q)
__CPROVER_requires(b >= 0 && b < Q)
__CPROVER_ensures(__CPROVER_return_value >= 0 && __CPROVER_return_value < Q)
{
    int32_t r1 = (int32_t) a * (int32_t) b;
    int64_t r2 = r1 * magic;
    int32_t r3 = (int32_t) (r2 / c);
    int32_t r4 = r3 * Q;
    int32_t r = r1 - r4;
    __CPROVER_assert(r >= 0, "r is natural");
    __CPROVER_assert(r < Q, "r less than Q");
    return (uint16_t) r;
}


void mod3329_harness()
{
    uint16_t x, y;
    uint16_t r;
    r = mod3329(x, y);
}

void mod3329a_harness()
{
    uint16_t x, y;
    uint16_t r;
    r = mod3329a(x, y);
}

void mod3329b_harness()
{
    uint16_t x, y;
    uint16_t r;
    r = mod3329b(x, y);
}

void mod3329c_harness()
{
    uint16_t x, y;
    uint16_t r;
    r = mod3329c(x, y);
}
