#include "ar.h"
#include <string.h>

void init_st (st dst)
{
    size_t i;
    for (i = 0; i < C; i++)
    __CPROVER_assigns(i, __CPROVER_object_whole(dst))
    __CPROVER_loop_invariant(i <= C)
    __CPROVER_loop_invariant(__CPROVER_forall { size_t j; (0 <= j && j < i) ==> dst[j] == 0 } )
    {
        dst[i] = 0;
    }
}

void init_st_harness()
{
    st dest;

    init_st(dest);
}
