#include <stdint.h>
#include "../common/cbmc.h"

#define Q 3329

uint16_t mod3329(uint16_t a, uint16_t b);

// No contracts here constraining range of a and b
uint16_t mod3329a(uint16_t a, uint16_t b);

// Now with contracts this time
uint16_t mod3329b(uint16_t a, uint16_t b)
__contract__(
  requires(a >= 0 && a < Q)
  requires(b >= 0 && b < Q)
);

// More contracts showing the range of the return value
uint16_t mod3329c(uint16_t a, uint16_t b)
__contract__(
  requires(a >= 0 && a < Q)
  requires(b >= 0 && b < Q)
  ensures(return_value >= 0 && return_value < Q)
);

// Montgomery reduction from the Kyber reference implementation
int16_t mr1(int32_t a)
__contract__(
  requires(a >= -32768 * Q)
  requires(a <= 32768 * Q - 1)
  ensures(return_value >= (-Q) + 1)
  ensures(return_value <= Q - 1)
  ensures(((return_value * 65536) - a) % Q == 0)
);

// Montgomery reduction from the Kyber reference implementation
// Alternative implementation
int16_t mr2(int32_t a)
__contract__(
  requires(a >= -32768 * Q)
  requires(a <= 32768 * Q - 1)
  ensures(return_value >= (-Q) + 1)
  ensures(return_value <= Q - 1)
  ensures(((__CPROVER_return_value * 65536) - a) % Q == 0)
);
