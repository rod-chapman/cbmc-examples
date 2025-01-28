#include <stdint.h>

#include "../common/cbmc.h"

// truncated square root of 2**31-1
#define INT32_ROOT_MAX 46340

int32_t isqrt(int32_t x)
__contract__(
  requires(x >= 0)
  ensures(0 <= return_value)
  ensures(return_value <= INT32_ROOT_MAX)
  ensures(return_value * return_value <= x)
  ensures(((int64_t)return_value + 1) * ((int64_t)return_value + 1) > (int64_t)x)
)
{
  int32_t upper, lower, middle;
  lower = 0;
  upper = INT32_ROOT_MAX + 1;
  while (lower + 1 != upper)
  __loop__(
    assigns(middle, lower, upper)
    invariant(0 <= lower && lower <= INT32_ROOT_MAX)
    invariant(0 <= upper && upper <= (INT32_ROOT_MAX + 1))
    invariant(lower * lower <= x)
        // cast to int64_t here to avoid overflow on *
    invariant((int64_t)upper * (int64_t)upper > (int64_t)x)
    decreases(upper - lower)
  )
  {
    middle = (lower + upper) / 2;
    if ((middle * middle) > x)
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
