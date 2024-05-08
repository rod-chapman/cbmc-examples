#include "str.h"

void tl1 (char *dst, size_t len)
{
    for (size_t i = 0; i < len; i++)
    {
        dst[i] = tolower(dst[i]);
    }
}

/////////////
// HARNESSES
/////////////

void tl1_harness()
{
    char st[8] = "HELLOROD";
    tl1(st, 8);
}
