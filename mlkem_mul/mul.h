#include <stdint.h>

#include "../common/cbmc.h"

#define Q 3329

// Multiplication of a * b mod Q, but to be done
// in cryptographic constant time. Use of C's predefined % operator
// is not permitted. Use of any "div" instruction in the generated
// code is not permitted.
uint32_t mul32(uint32_t a, uint32_t b)
__contract__(
  requires(a < Q)
  requires(b < Q)
  ensures(return_value == (a * b) % Q);
);

uint32_t mul32_proved(uint32_t a, uint32_t b)
__contract__(
  requires(a < Q)
  requires(b < Q)
  ensures(return_value == (a * b) % Q)
);

// As above, but done using 64-bit Montgomery division
uint32_t mul64(uint32_t a, uint32_t b)
__contract__(
  requires(a < Q)
  requires(b < Q)
  ensures(return_value == (a * b) % Q);
);

// As above, but done using 64-bit arithmetic and C's % operator,
// as a reference for comparison and equivalence proof.
uint32_t mul_ref(uint32_t a, uint32_t b)
__contract__(
  requires(a < Q)
  requires(b < Q)
  ensures(return_value == (a * b) % Q);
);
