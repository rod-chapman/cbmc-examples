#include <assert.h>
#include <stdbool.h>
#include <stddef.h>

#define N 16

void main()
{
  int a[N];
  a[10] = 0;
  bool flag = true;
  for(size_t j = 0; j < N; ++j)
  __CPROVER_assigns(j, __CPROVER_object_whole(a))
  __CPROVER_loop_invariant(j <= N)
  {
      for(size_t i = 0; i < N; ++i)
      __CPROVER_assigns(i, __CPROVER_object_whole(a))
      __CPROVER_loop_invariant(i <= N)

//////////////
// This version terminates fine
//      __CPROVER_loop_invariant(__CPROVER_forall { int k; (0 <= k && k <= N) ==> (k<i ==> a[k] == 1) })

// This version causes non-termination and repeated running of Z3. Only difference is "size_t" instead of "int"
// for the quantified variable
      __CPROVER_loop_invariant(__CPROVER_forall { size_t k; (0 <= k && k <= N) ==> (k<i ==> a[k] == 1) })
//////////////
      {
          a[i] = 1;
      }
  }
  assert(a[10] == 1);
}
