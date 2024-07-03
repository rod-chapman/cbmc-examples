#include <stdint.h>

int32_t inc2 (int32_t x)
__CPROVER_requires(x < 10)
__CPROVER_ensures(__CPROVER_return_value == x + 2);
