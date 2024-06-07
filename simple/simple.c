#include "simple.h"

int32_t average (int32_t a, int32_t b)
{
    return (a + b) / 2;
}

void average_harness()
{
    int32_t a;
    int32_t b;
    int32_t result;
    result = average(a, b);
}
