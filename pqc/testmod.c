#include <stdlib.h>
#include <stdio.h>
#include "crypto.h"

int main()
{
    for (uint16_t i = 0; i < Q; i++)
    {
        printf("Outer loop i = %u\n", i);
        for (uint16_t j = 0; j < Q; j++)
        {
            uint16_t r1 = mod3329 (i, j);
            uint16_t r2 = mod3329b (i, j);
            if (r1 != r2)
            {
                printf("Fail!\n");
                exit(0);
            }
        }
    }

    printf("Pass!\n");
    return 0;
}
