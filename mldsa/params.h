#ifndef ML_DSA_PARAMS_H
#define ML_DSA_PARAMS_H

// The only defined parameters are those that don't depend
// on the parameter set. All other parameters are specified
// in ml_dsa_params structure that is unique for each parameter
// set (ML-DSA 44/65/87).
#define ML_DSA_SEEDBYTES 32
#define ML_DSA_CRHBYTES 64
#define ML_DSA_TRBYTES 64
#define ML_DSA_RNDBYTES 32
#define ML_DSA_N 256
#define ML_DSA_Q 8380417
#define ML_DSA_D 13
#define ML_DSA_POLYT1_PACKEDBYTES  320
#define ML_DSA_POLYT0_PACKEDBYTES  416

#endif
