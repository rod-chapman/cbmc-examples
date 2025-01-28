#include "crypto.h"

uint16_t mod3329(uint16_t a, uint16_t b)
{
  // Naive implementation using C's % operator. This is functionally
  // correct, but not guaranteed to execute in constant-time. In particular
  // some compilers will generate a "divide" instruction.
  uint32_t r = (uint32_t)a * (uint32_t)b;
  r = r % Q;
  return (uint16_t)r;
}

const int64_t c = 1UL << 37;
const int64_t magic = c / Q;

uint16_t mod3329a(uint16_t a, uint16_t b)
{
  // Potential overflow reported here for "*" since we don't
  // know the upper-bound on a and b
  int32_t r1 = (int32_t)a * (int32_t)b;

  // Modular reduction written out explicitly, using the
  // Montgomery division trick from PLDI 1994.
  int64_t r2 = r1 * magic;
  int32_t r3 = (int32_t)(r2 / c);
  int32_t r4 = r3 * Q;
  int32_t r = r1 - r4;

  // Potential overflow on type conversion here, since
  // we don't know enough about the range of r
  return (uint16_t)r;
}


uint16_t mod3329b(uint16_t a, uint16_t b)
{
  // With pre-conditions on a and b, verification of type-safety
  // is successful this time.
  int32_t r1 = (int32_t)a * (int32_t)b;
  int64_t r2 = r1 * magic;
  int32_t r3 = (int32_t)(r2 / c);
  int32_t r4 = r3 * Q;
  int32_t r = r1 - r4;
  return (uint16_t)r;
}


uint16_t mod3329c(uint16_t a, uint16_t b)
{
  int32_t r1 = (int32_t)a * (int32_t)b;
  int64_t r2 = r1 * magic;
  int32_t r3 = (int32_t)(r2 / c);
  int32_t r4 = r3 * Q;
  int32_t r = r1 - r4;

  // Assert range of r to meet post-condition
  cassert(r >= 0);
  cassert(r < Q);
  return (uint16_t)r;
}


#define QINV -3327  // q^-1 mod 2^16

// This code from the Kyber reference implementation.
int16_t mr1(int32_t a)
{
  int16_t t;

  t = (int16_t)a * QINV;  // Proof fails here on overflow in type conversion
  t = (a - (int32_t)t * Q) >> 16;
  return t;
}


// Alternative implementation, avoiding implementation-defined
// casts and >> on a negative integer
int16_t mr2(int32_t a)
{
  // -3327 -> uint16_t == -3327 + 65536 == 62209
  const uint16_t UQINV = 62209;

  // By default, CBMC is too strict about signed to unsigned conversion,
  // which are well-defined according to C17 6.3.1.3(2)
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"
#pragma CPROVER check disable "signed-overflow"
  // int32_t -> uint16_t - add or substract 65536 until in range
  //  e.g. -1 -> 65535
  uint16_t ua = (uint16_t)a;
  uint32_t t1 = (uint32_t)(ua * UQINV);
#pragma CPROVER check pop

  t1 = t1 % 65536;

  // t1 now in 0 .. 65535
  // so conversion to int32_t is well-defined
  int32_t t1s = (int32_t)t1;

  t1s = t1s - (65536 * (t1s >= 32768));

  // t1s now in -32768 .. 32767
  int32_t t4 = t1s * Q;
  int32_t t5 = a - t4;

  cassert(t5 % 65536 == 0);
  // Therefore "/" is equivalent to >> for negative t5, but "/" is
  // not implementation-defined
  int32_t t6 = t5 / 65536;

  // t6 now in -3328 .. 3328, therefore conversion to int16_t is well-defined
  int16_t result = (int16_t)t6;

  return result;
}


void mod3329_harness()
{
  uint16_t x, y;
  uint16_t r;
  r = mod3329(x, y);
}

void mod3329a_harness()
{
  uint16_t x, y;
  uint16_t r;
  r = mod3329a(x, y);
}

void mod3329b_harness()
{
  uint16_t x, y;
  uint16_t r;
  r = mod3329b(x, y);
}

void mod3329c_harness()
{
  uint16_t x, y;
  uint16_t r;
  r = mod3329c(x, y);
}

void mr1_harness()
{
  int32_t a;
  int16_t r;
  r = mr1(a);
}

void mr2_harness()
{
  int32_t a;
  int16_t r;
  r = mr2(a);
}
