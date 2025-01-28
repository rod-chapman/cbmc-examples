#include <stdint.h>

#include "../common/cbmc.h"

int32_t inc2(int32_t x)
__contract__(
  requires(x < 10)
  ensures(return_value == x + 2)
);
