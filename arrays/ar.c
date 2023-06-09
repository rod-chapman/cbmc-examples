#include "ar.h"

void f1 (uint32_t *s)
{
    s[0] ^= 0xDEADBEEF;
    s[1] ^= 0xBEEFDEAD;
    s[2] ^= 0xDEADBEEF;
    s[3] ^= 0xBEEFDEAD;
    s[4] ^= 0xDEADBEEF;
    s[5] ^= 0xBEEFDEAD;
    s[6] ^= 0xDEADBEEF;
    s[7] ^= 0xBEEFDEAD;
}

void f2 (uint32_t s[static C])
{
    s[0] ^= 0xDEADBEEF;
    s[1] ^= 0xBEEFDEAD;
    s[2] ^= 0xDEADBEEF;
    s[3] ^= 0xBEEFDEAD;
    s[4] ^= 0xDEADBEEF;
    s[5] ^= 0xBEEFDEAD;
    s[6] ^= 0xDEADBEEF;
    s[7] ^= 0xBEEFDEAD;
//    s[8] ^= 0xBEEFDEAD; // this fails as expected
}

void f3 (st s)
{
    s[0] ^= 0xDEADBEEF;
    s[1] ^= 0xBEEFDEAD;
    s[2] ^= 0xDEADBEEF;
    s[3] ^= 0xBEEFDEAD;
    s[4] ^= 0xDEADBEEF;
    s[5] ^= 0xBEEFDEAD;
    s[6] ^= 0xDEADBEEF;
    s[7] ^= 0xBEEFDEAD;
//    s[8] ^= 0xBEEFDEAD; // this fails as expected
}

uint32_t arsum(const uint8_t *data, size_t num_blocks)
{
    uint8_t *current_byte_ptr = data;
    const uint8_t *last_byte_ptr = data + (num_blocks * BLOCK_SIZE) - 1;
    uint32_t sum = 0;

    __CPROVER_assert(__CPROVER_pointer_in_range_dfcc(data, current_byte_ptr, last_byte_ptr), "Oops");

    for(; num_blocks--;)
    __CPROVER_assigns(num_blocks, sum, current_byte_ptr)
    __CPROVER_loop_invariant(num_blocks > 0)
    {
        sum += *current_byte_ptr;
        current_byte_ptr++;
        sum += *current_byte_ptr;
        current_byte_ptr++;
        sum += *current_byte_ptr;
        current_byte_ptr++;
        sum += *current_byte_ptr;
        current_byte_ptr++;
    }
    return sum;
}


void f1_harness()
{
    uint32_t st[C] = { 0 };
    f1(st);
}

void f2_harness()
{
    uint32_t st[C] = { 0 };
    f2(st);
}

void f3_harness()
{
    st t = { 0 };
    f3(t);
}

void arsum_harness()
{
    uint8_t d[8] = { 1, 2, 3, 4, 5, 6, 7, 8 };
    uint32_t r;
    r = arsum(d, 2);
}
