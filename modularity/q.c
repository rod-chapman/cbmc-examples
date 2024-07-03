#include "q.h"
#include "p.h"

int32_t inc2 (int32_t x)
{
    int32_t r = x;
    r = inc(r);
    r = inc(r);
    return r;
}

void inc2_harness()
{
    int32_t x, y;
    y = inc2(x);
}
