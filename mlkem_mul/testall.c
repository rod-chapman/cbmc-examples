#include <stdio.h>

#include "mul.h"


int main()
{

  for (uint32_t a = 0; a < Q; a++)
  {
    for (uint32_t b = 0; b < Q; b++)
    {
      uint32_t r1 = mul32(a,b);
      uint32_t r2 = mul64(a,b);
      uint32_t r3 = mul_ref(a,b);

      if (r1 != r2)
      {
        printf("Fail r1 != r2 with %u, %u, %u, %u\n", a, b, r1, r2);
      }

      if (r1 != r3)
      {
        printf("Fail r1 != r3 with %u, %u, %u, %u\n", a, b, r1, r3);
      }

      if (r2 != r3)
      {
        printf("Fail r2 != r3 with %u, %u, %u, %u\n", a, b, r2, r3);
      }

    }
  }
  return 0;
}
