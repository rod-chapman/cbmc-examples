#include <stdalign.h>
#include <stdint.h>
#include "../common/cbmc.h"

typedef uint64_t gf[4];

void add(gf x)
__contract__(
  requires(alignof(x) == 16)
) { x[0] = x[0] + 1; }

int main()
{
  alignas(16) gf gf16 = {1};
  add(gf16);  // should be OK, but fails?
}

void main_harness() { int y = main(); }
