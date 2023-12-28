#include <stdio.h>

#ifdef CBMC
#else
#define __CPROVER_assert(...)
#endif

int ub1(void) {
  volatile int x = 0;
  int y;

  // This statement exhibits both unspecified behaviour on evalation order,
  // and also Undefined Behaviour, owing to more than one side-effect to
  // a single object before a single sequence point
  y = (x = 2) + (x = 1);

//  __CPROVER_assert(y == 0, "Oops0..."); // FAILURE
//  __CPROVER_assert(y == 1, "Oops1..."); // FAILURE
  __CPROVER_assert(y == 2, "Oops2..."); // SUCCESS ?!?!?
//  __CPROVER_assert(y == 3, "Oops3..."); // FAILURE
//  printf ("y is %d\n", y); // Prints "y is 3" with clang 14.0.3

}

int ub1_harness(void)
{
    ub1();
}

int main(void)
{
    ub1();
    return 0;
}
