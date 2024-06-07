#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <limits.h>

#ifdef CBMC
#else
#define __CPROVER_assigns(...)
#define __CPROVER_decreases(...)
#define __CPROVER_assert(...)
#define __CPROVER_requires(...)
#define __CPROVER_ensures(...)
#define __CPROVER_loop_invariant(...)
#endif

int32_t average (int32_t a, int32_t b)
__CPROVER_requires(a >= 0 && b >= 0)
__CPROVER_ensures(__CPROVER_return_value == (a + b) / 2)
__CPROVER_ensures(__CPROVER_return_value >= 0);
