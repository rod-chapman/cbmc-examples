#include "poly.h"

void mvm(polyvec *out, const polyvec a[MLKEM_K], const polyvec *v,
                const polyvec_mulcache *vc)  // clang-format off
  REQUIRES(IS_FRESH(out, sizeof(polyvec)))
  REQUIRES(IS_FRESH(a, sizeof(polyvec) * MLKEM_K))
  REQUIRES(IS_FRESH(v, sizeof(polyvec)))
  REQUIRES(IS_FRESH(vc, sizeof(polyvec_mulcache)))
  REQUIRES(FORALL(int, k0, 0, MLKEM_K - 1,
   FORALL(int, k1, 0, MLKEM_K - 1,
     ARRAY_ABS_BOUND(a[k0].vec[k1].coeffs, 0, MLKEM_N - 1, (MLKEM_Q - 1)))))
  ASSIGNS(OBJECT_WHOLE(out))
// clang-format on
{
  for (int i = 0; i < MLKEM_K; i++)
  ASSIGNS(i, OBJECT_WHOLE(out))
  INVARIANT(i >= 0 && i <= MLKEM_K)
  {
    polyvec_basemul_acc_montgomery_cached(&out->vec[i], &a[i], v, vc);
  }
}

void mvm_harness(void) {
  polyvec *out, *a, *v;
  polyvec_mulcache *vc;
  mvm(out, a, v, vc);
}
