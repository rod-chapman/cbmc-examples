#include <stdint.h>

#ifdef CBMC
#else
#define __CPROVER_assigns(...)
#define __CPROVER_decreases(...)
#define __CPROVER_assert(...)
#define __CPROVER_requires(...)
#define __CPROVER_ensures(...)
#define __CPROVER_loop_invariant(...)
#endif

// truncated square root of 2**31-1
#define INT32_ROOT_MAX 46340

int32_t isqrt(int32_t x)
__CPROVER_requires (x >= 0)
__CPROVER_ensures  (0 <= __CPROVER_return_value &&
                    __CPROVER_return_value <= INT32_ROOT_MAX &&
                    (__CPROVER_return_value * __CPROVER_return_value <= x) &&
                    (((int64_t) __CPROVER_return_value + 1 ) * ((int64_t) __CPROVER_return_value + 1) > (int64_t) x))
{
    int32_t upper, lower, middle;
    lower = 0;
    upper = INT32_ROOT_MAX + 1;
    while(lower + 1 != upper)
    __CPROVER_assigns(middle, lower, upper)
    __CPROVER_loop_invariant(0 <= lower && lower <= INT32_ROOT_MAX)
    __CPROVER_loop_invariant(0 <= upper && upper <= (INT32_ROOT_MAX + 1))
    __CPROVER_loop_invariant(lower * lower <= x)
    // cast to int64_t here to avoid overflow on *
    __CPROVER_loop_invariant((int64_t) upper * (int64_t) upper > (int64_t) x)
    __CPROVER_decreases(upper - lower)
    {
        middle = (lower + upper) / 2;
        if((middle * middle) > x)
            upper = middle;
        else
            lower = middle;
    }
    return lower;
}

void isqrt_harness()
{
    int32_t x, y;
    y = isqrt(x);
}
