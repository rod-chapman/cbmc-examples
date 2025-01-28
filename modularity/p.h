#include <stdint.h>
#include "../common/cbmc.h"

int32_t inc(int32_t x)
__contract__(
  requires(x < 20)
  ensures(return_value == x + 1)
);
