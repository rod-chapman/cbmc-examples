#include <stdint.h>

int32_t inc (int32_t x)
__CPROVER_requires(x < 20)
__CPROVER_ensures(__CPROVER_return_value == x + 1);
