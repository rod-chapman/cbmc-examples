#include <ctype.h>
#include <stdint.h>
#include <stddef.h>
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

void tl1 (char *dst, size_t len)
__CPROVER_requires(__CPROVER_is_fresh(dst, len))
__CPROVER_assigns(__CPROVER_object_whole(dst))
__CPROVER_ensures(__CPROVER_forall { int i; (0 <= i && i < len) ==> dst[i] == __CPROVER_uninterpreted_tolower(__CPROVER_old(dst[i])) });
