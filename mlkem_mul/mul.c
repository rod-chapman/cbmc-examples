#include "mul.h"

#define P32 20
#define C32 1048576 // 2**P
#define MAGIC32 (C32 / Q + 1) // 315

uint32_t mul32 (uint32_t a, uint32_t b)
{
    // (a * b) % Q == (a * b) - ((a * b) / Q) * Q
    // but we compute the division using the
    // Montgomery trick from PLDI'94, using
    // the multiply-and-shift constants declared above.
    // These have been deliberately chosen in this case to
    // avoid the need for a 64 bit multiply...

    // In particular, note that with the precondition on a and b,
    // a * b * MAGIC32 <= 3328 * 3328 * 315 < 2**32-1
    // so it CAN be done in unsigned 32 bit arithmetic.
    uint32_t m = a * b;
    uint32_t m2;
    int32_t  r;

    m2 = (m * MAGIC32) >> P32;

    m2 = m2 * Q;

    r = (int32_t) m - (int32_t) m2;

    r = r + (Q * (r < 0));
    return (uint32_t) r;
}

uint32_t mul32_proved (uint32_t a, uint32_t b)
{
    // As above, but using intermediate assertions
    uint32_t m = a * b;
    uint32_t m2;
    int32_t  r;

    m2 = (m * MAGIC32) >> P32;

    // Owing to the error-bound on Magic, M2 is either
    // "just right" or "too big by 1"
    __CPROVER_assert (((m2 == m / Q) ||
                       (m2 == (m / Q) + 1)), "assertion 1");

    m2 = m2 * Q;

    __CPROVER_assert (((m2 == (m / Q) * Q) ||
                       (m2 == ((m / Q) * Q) + Q)), "assertion 2");

    r = (int32_t) m - (int32_t) m2;

    __CPROVER_assert (((r == (int32_t) m - (int32_t) ((m / Q) * Q)) ||
                       (r == (int32_t) m - (int32_t) ((m / Q) * Q + Q))), "assertion 3");

    r = r + (Q * (r < 0));

    __CPROVER_assert (((uint32_t) r == m % Q), "assertion 4");

    return (uint32_t) r;
}



#define P64 37
#define C64 137438953472 // 2**P
#define MAGIC64 (C64 / Q) // 41_285_357
uint32_t mul64 (uint32_t a, uint32_t b)
{
    uint64_t m = (uint64_t) (a * b);
    uint64_t m2;
    uint32_t  r;

    m2 = (m * MAGIC64) >> P64;

    m2 = m2 * Q;

    r = (int32_t) m - (int32_t) m2;

    return r;
}





uint32_t mul_ref (uint32_t a, uint32_t b)
{
  uint64_t t = (uint64_t) a * (uint64_t) b;
  uint32_t t2 = (int32_t) t;
  return t2 % Q;
}

void mul32_harness()
{
    uint32_t a, b, r;
    r = mul32 (a, b);
}

void mul32_proved_harness()
{
    uint32_t a, b, r;
    r = mul32_proved (a, b);
}
