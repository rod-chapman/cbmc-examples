#include <assert.h>
#include <stdbool.h>
#include <stddef.h>

#define N 16

void f(int r[N])
__CPROVER_requires(__CPROVER_forall { int k; (0 <= k && k < N) ==> (r[k] >= 10 && r[k] <= 20) } )
__CPROVER_assigns(__CPROVER_object_whole(r))
__CPROVER_ensures(__CPROVER_forall { int k; (0 <= k && k < N) ==> (r[k] >= 11 && r[k] <= 21) } )
{
    for (int j = 0; j < N; j++)
    __CPROVER_assigns(j, __CPROVER_object_whole(r))
    __CPROVER_loop_invariant(j >= 0)
    __CPROVER_loop_invariant(j <= N)
    __CPROVER_loop_invariant(__CPROVER_forall { int k; (0 <= k && k <= j - 1) ==> (r[k] >= 11 && r[k] <= 21) } )
    __CPROVER_loop_invariant(__CPROVER_forall { int k; (j <= k && k < N)      ==> (r[k] >= 10 && r[k] <= 20) } )
    __CPROVER_decreases(N - j)
    {
        int t = r[j];
        __CPROVER_assert(t == __CPROVER_loop_entry(r[j]), "Initial value of r[j]");
        r[j] = t + 1;
    }
}

void f_harness()
{
    int x[N];
    f(x);
}
