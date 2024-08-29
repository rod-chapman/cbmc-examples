#include <stdint.h>

#ifdef CBMC
#else
#define __CPROVER_requires(a)
#define __CPROVER_ensures(a)
#define __CPROVER_assert(a)
#endif

#define Q 3329

// Multiplication of a * b mod Q, but to be done
// in cryptographic constant time. Use of C's predefined % operator
// is not permitted. Use of any "div" instruction in the generated
// code is not permitted.
uint32_t mul (uint32_t a, uint32_t b)
__CPROVER_requires(a < Q)
__CPROVER_requires(b < Q)
__CPROVER_ensures(__CPROVER_return_value == (a * b) % Q);

uint32_t mul2 (uint32_t a, uint32_t b)
__CPROVER_requires(a < Q)
__CPROVER_requires(b < Q)
__CPROVER_ensures(__CPROVER_return_value == (a * b) % Q);
