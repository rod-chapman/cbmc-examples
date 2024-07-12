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

#define C 8

typedef uint32_t st[C];

void init_st (st dst)
__CPROVER_requires(__CPROVER_is_fresh(dst, sizeof(st)))
__CPROVER_assigns(__CPROVER_object_whole(dst))
__CPROVER_ensures(__CPROVER_forall { unsigned i; (0 <= i && i < C) ==> dst[i] == 0 });


// Change 'i' to 'k' and all is well?
//__CPROVER_ensures(__CPROVER_forall { unsigned k; (0 <= k && k < C) ==> dst[k] == 0 });
