#include "mul.h"

#define P 20
#define C 1048576 // 2**P
#define MAGIC (C / Q + 1) // 315

uint32_t mul (uint32_t a, uint32_t b)
{
    // (a * b) % Q == (a * b) - ((a * b) / Q) * Q
    // but we compute the division using the
    // Montgomery trick from PLDI'94, using
    // the multiply-and-shift constants declared above.
    // These have been deliberately chosen in this case to
    // avoid the need for a 64 bit multiply...

    // In particular, note that with the precondition on a and b,
    // a * b * MAGIC <= 3328 * 3328 * 315 < 2**32-1
    // so it CAN be done in unsigned 32 bit arithmetic.
    uint32_t m = a * b;
    uint32_t m2;
    int32_t  r;

    m2 = (m * MAGIC) >> P;

    m2 = m2 * Q;

    r = (int32_t) m - (int32_t) m2;

    r = r + (Q * (r < 0));
    return (uint32_t) r;
}

uint32_t mul2 (uint32_t a, uint32_t b)
{
    // As above, but using intermediate assertions
    uint32_t m = a * b;
    uint32_t m2;
    int32_t  r;

    m2 = (m * MAGIC) >> P;

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

void mul_harness()
{
    uint32_t a, b, r;
    r = mul (a, b);
}

void mul2_harness()
{
    uint32_t a, b, r;
    r = mul2 (a, b);
}
