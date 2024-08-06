#include <stdint.h>
#include <stdalign.h>

#ifdef CBMC
#else
#define __CPROVER_assigns(...)
#define __CPROVER_decreases(...)
#define __CPROVER_assert(...)
#define __CPROVER_requires(...)
#define __CPROVER_ensures(...)
#define __CPROVER_loop_invariant(...)
#endif

typedef uint64_t gf[4];

void add(gf x)
__CPROVER_requires(alignof(x) == 16)
{
    x[0] = x[0] + 1;
}


int main()
{
    alignas(16) gf gf16 = { 1 };
    add(gf16); // should be OK, but fails?

//    alignas(8) gf gf8 = { 2 };
//    add(gf8); // should fail

//    gf gf_default = { 3 };
//    add(gf_default); // should fail - alignment unknown

}

void main_harness()
{
    int y = main();
}
