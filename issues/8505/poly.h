#include <stddef.h>
#include <stdint.h>

#define MLKEM_N 256
#define MLKEM_K 3
#define MLKEM_Q 3329

#ifdef CBMC
#define ASSIGNS(...) __CPROVER_assigns(__VA_ARGS__)
#define REQUIRES(...) __CPROVER_requires(__VA_ARGS__)
#define ENSURES(...) __CPROVER_ensures(__VA_ARGS__)
#define INVARIANT(...) __CPROVER_loop_invariant(__VA_ARGS__)
#define OBJECT_UPTO(...) __CPROVER_object_upto(__VA_ARGS__)
#define OBJECT_WHOLE(...) __CPROVER_object_whole(__VA_ARGS__)
#define IS_FRESH(...) __CPROVER_is_fresh(__VA_ARGS__)

#define FORALL(type, qvar, qvar_lb, qvar_ub, predicate)          \
  __CPROVER_forall                                               \
  {                                                              \
    type qvar;                                                   \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) ==> (predicate) \
  }

#define CBMC_CONCAT_(left, right) left##right
#define CBMC_CONCAT(left, right) CBMC_CONCAT_(left,right)

#define ARRAY_BOUND_CORE(indextype, qvar, qvar_lb, qvar_ub, array_var, \
                        value_lb, value_ub)                           \
  __CPROVER_forall                                                    \
  {                                                                   \
    indextype qvar;                                                   \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) ==>                  \
          (((value_lb) <= (array_var[(qvar)])) &&                     \
           ((array_var[(qvar)]) <= (value_ub)))                       \
  }

#define ARRAY_BOUND(array_var, qvar_lb, qvar_ub,                  \
                        value_lb, value_ub)                           \
    ARRAY_BOUND_CORE(int, CBMC_CONCAT(_cbmc_idx,__LINE__),        \
     (qvar_lb), (qvar_ub), (array_var), (value_lb), (value_ub))

// clang-format on

// Wrapper around ARRAY_BOUND operating on absolute values
#define ARRAY_ABS_BOUND(arr, lb, ub, k) \
  ARRAY_BOUND((arr), (lb), (ub), (-(k)), (k))

#else

#define ASSIGNS(...)
#define REQUIRES(...)
#define ENSURES(...)

#endif

typedef struct {
  int16_t coeffs[MLKEM_N];
} poly;

typedef struct {
  int16_t coeffs[MLKEM_N >> 1];
} poly_mulcache;

typedef struct {
  poly vec[MLKEM_K];
} polyvec;

typedef struct {
  poly_mulcache vec[MLKEM_K];
} polyvec_mulcache;

void polyvec_basemul_acc_montgomery_cached(
    poly *r, const polyvec *a, const polyvec *b,
    const polyvec_mulcache *b_cache)
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(a, sizeof(polyvec)))
REQUIRES(IS_FRESH(b, sizeof(polyvec)))
REQUIRES(IS_FRESH(b_cache, sizeof(polyvec_mulcache)))
REQUIRES(FORALL(int, k1, 0, MLKEM_K - 1,
 ARRAY_ABS_BOUND(a->vec[k1].coeffs, 0, MLKEM_N - 1, (MLKEM_Q - 1))))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)));
