#include "ar.h"
#include <string.h>

void f1(uint32_t *s)
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

void f2(uint32_t s[static C])
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

void f3(st s)
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

uint32_t arsum_blocks1(const uint8_t *data, size_t num_blocks)
{
  // Form uint32_t sum of bytes denoted by data.
  // Counting in blocks of 4 bytes at a time.

  // This implementation uses array indexing rather than pointer arithmetic
  uint32_t sum = 0;
  for (size_t current_block = 0; current_block < num_blocks; current_block++)
  __loop__(
      invariant(current_block <= num_blocks)
    )
  {
    size_t block_base = current_block * BLOCK_SIZE;
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    sum += data[block_base];
    sum += data[block_base + 1];
    sum += data[block_base + 2];
    sum += data[block_base + 3];
#pragma CPROVER check pop
  }
  return sum;
}

uint32_t arsum_blocks2(const uint8_t *data, size_t num_blocks)
{
  // Form uint32_t sum of bytes denoted by data.
  // Counting in blocks of 4 bytes at a time.

  // This implementation uses pointer arithmetic
  uint8_t *current_byte_ptr = data;
  const uint8_t *last_block_ptr = data + ((num_blocks - 1) * BLOCK_SIZE);
  uint32_t sum = 0;
  size_t blocks_to_go = num_blocks;

  for (; blocks_to_go >= 1; blocks_to_go--)
  __loop__(
    invariant(blocks_to_go <= num_blocks)
    invariant(current_byte_ptr == (data + (num_blocks - blocks_to_go) * BLOCK_SIZE))
  )
  {
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    sum += *current_byte_ptr;
    current_byte_ptr++;
    sum += *current_byte_ptr;
    current_byte_ptr++;
    sum += *current_byte_ptr;
    current_byte_ptr++;
    sum += *current_byte_ptr;
    current_byte_ptr++;
#pragma CPROVER check pop
  }
  return sum;
}


uint32_t arsum_bytes1(const uint8_t *data, size_t num_bytes)
{
  // This implementation uses array indexing
  uint32_t sum = 0;
  for (size_t idx = 0; idx < num_bytes; idx++)
  __loop__(
    invariant(idx <= num_bytes)
  )
  {
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    sum += data[idx];
#pragma CPROVER check pop
  }
  return sum;
}

uint32_t arsum_bytes2(const uint8_t *data, size_t num_bytes)
{
  // This implementation uses explicit pointer arithmetic instead
  // of array indexing
  uint8_t *current_byte_ptr = data;
  uint32_t sum = 0;
  size_t bytes_to_go = num_bytes;
  for (; bytes_to_go >= 1; bytes_to_go--)
  __loop__(
    invariant(bytes_to_go <= num_bytes)
    invariant(current_byte_ptr == (data + (num_bytes - bytes_to_go)))
  )
  {
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    sum += *current_byte_ptr;
    current_byte_ptr++;
#pragma CPROVER check pop
  }
  return sum;
}

int32_t arsum_swords(const int32_t *data, const int32_t datalen)
{
  int32_t sum = 0;

  for (int32_t idx = 0; idx < datalen; idx++)
  __loop__(
    invariant(idx >= 0 && idx <= datalen)
    invariant(sum >= idx * DATA_MIN) // Lower bound on sum in terms of idx
    invariant(sum <= idx * DATA_MAX) // Upper bound on sum in terms of idx
  )
  {
    sum += data[idx];
  }
  return sum;
}


// Array assignment - element by element copy
void assign_st1(st dst, const st src)
{
  dst[0] = src[0];
  dst[1] = src[1];
  dst[2] = src[2];
  dst[3] = src[3];
  dst[4] = src[4];
  dst[5] = src[5];
  dst[6] = src[6];
  dst[7] = src[7];
}

// Array assignment by loop copy
void assign_st2(st dst, const st src)
{
  for (size_t i = 0; i < C; i++)
  __loop__(
    invariant(i <= C)
    invariant(forall(j, 0, i, dst[j] == src[j]))
  )
  {
    dst[i] = src[i];
  }

  // Substitute i == C into the loop invariant to get:
  cassert(forall(j, 0, C, dst[j] == src[j]));
}

// Array assignment using memcpy()
void assign_st3(st dst, const st src) { memcpy(dst, src, sizeof(st)); }

void init_st(st dst)
{
  size_t i;
  for (i = 0; i < C; i++)
  __loop__(
    invariant(i <= C)
    invariant(forall(j, 0, i, dst[j] == 0))
  )
  {
    dst[i] = 0;
  }
}

void zero_slice(uint8_t *dst, size_t len)
{
  size_t i;
  for (i = 0; i < len; i++)
  __loop__(
    assigns(i, memory_slice(dst, len)) // Needed for speed of verification
    invariant(i <= len)
    invariant(forall(j, 0, i, dst[j] == 0))
  )
  {
    dst[i] = 0;
  }
}

void zero_array_ts(uint8_t *dst, unsigned len)
{
  for (unsigned i = 0; i < len; i++)
  __loop__(
    invariant(i <= len)
  )
  {
    dst[i] = 0;
  }
}

void zero_array_correct(uint8_t *dst, unsigned len)
{
  for (unsigned i = 0; i < len; i++)
  __loop__(
    invariant(i <= len)
    invariant(forall(j, 0, i, dst[j] == 0))
  )
  {
    dst[i] = 0;
  }
}



bool constant_time_equals_strict(const uint8_t *const a, const uint8_t *const b,
                                 const uint32_t len)
{
  bool arrays_equal = true;
  /* iterate over each byte in the slices */
  for (uint32_t i = 0; i < len; i++)
  __loop__(
    invariant(i <= len)
    invariant(arrays_equal == forall(j, 0, i, a[j] == b[j]))
  )
  {
    arrays_equal = arrays_equal && (a[i] == b[i]);
  }

  cassert(arrays_equal == forall(j, 0, len, a[j] == b[j]));
  return arrays_equal;
}

bool constant_time_equals_total(const uint8_t *const a, const uint8_t *const b,
                                const uint32_t len)
{
  if (a != NULL && b != NULL)
  {
    return constant_time_equals_strict(a, b, len);
  }
  else
  {
    return false;
  }
}

int ctcc(uint8_t *dst, const uint8_t *src, uint32_t len, uint8_t dont)
{
  uint8_t mask = ((dont == 0) * 0xff);

  /* dont = 0 : mask = 0xff */
  /* dont > 0 : mask = 0x00 */
  cassert(mask == (dont == 0 ? 0xff : 0x00));

  for (size_t i = 0; i < len; i++)
  __loop__(
    invariant(i <= len)
    invariant(forall(j, 0, i, dst[j] == (dont == 0 ? src[j] : loop_entry(dst)[j])))
  )
  {
    uint8_t old = dst[i];
    uint8_t diff = (old ^ src[i]) & mask;
    dst[i] = old ^ diff;
  }

  return 0;
}

int ctunpad(uint8_t *dst, const uint8_t *src, uint32_t srclen, uint32_t dstlen)
{
  size_t first_padding_byte_index = 2;
  size_t first_data_byte_index = srclen - dstlen;
  size_t zero_byte_index = first_data_byte_index - 1;
  uint8_t dont_copy;

  dont_copy = src[0] | (src[1] ^ 0x02);
  dont_copy = dont_copy | src[zero_byte_index];

  for (size_t i = first_padding_byte_index; i < zero_byte_index; i++)
  __loop__(
    invariant(i <= zero_byte_index)
    invariant(zero_byte_index < srclen)
  )
  {
    dont_copy = dont_copy | src[i];
  }

  return ctcc(dst, &src[first_data_byte_index], dstlen, dont_copy);
}


void inc_vector(vector v)
{
  for (unsigned i = 0; i < LC; i++)
  __loop__(
    assigns(i, object_whole(v))
    invariant(i <= LC)
    invariant(forall(j2, i, LC, v[j2] == loop_entry(* (vector *)v)[j2]))
    invariant(forall(j3, 0,  i, v[j3] == loop_entry(* (vector *)v)[j3] + 1))
  )
  {
    v[i]++;
  }
}


void inc_matrix(matrix m)
{
  for (unsigned i = 0; i < LC; i++)
  __loop__(
    assigns(i, object_whole(m))
    invariant(i <= LC)
    invariant(forall(j0, i, LC,
                     forall(k0, 0, LC, m[j0][k0] == loop_entry(* (matrix *)m)[j0][k0])))
    invariant(forall(j1, 0, i,
                     forall(k1, 0, LC, m[j1][k1] == loop_entry(* (matrix *)m)[j1][k1] + 1)))
  )
  {
    inc_vector(m[i]);
  }
}

int condmod(int16_t v[256])
{
  if (v[0] > 3)
  {
    // Bounds on v increase by 1
    v[0] += 1;
    return 0;
  }
  else
  {
    // v[] is left unmodified
    return -1;
  }
}

/////////////
// HARNESSES
/////////////

void f1_harness()
{
  uint32_t st[C] = {0};
  f1(st);
}

void f2_harness()
{
  uint32_t st[C] = {0};
  f2(st);
}

void f3_harness()
{
  st t = {0};
  f3(t);
}

void arsum_blocks1_harness()
{
  uint8_t *d;
  uint32_t r;
  size_t n;
  r = arsum_blocks1(d, n);
}

void arsum_blocks2_harness()
{
  uint8_t *d;
  uint32_t r;
  size_t n;
  r = arsum_blocks2(d, n);
}

void arsum_bytes1_harness()
{
  uint8_t *d;
  uint32_t r;
  size_t n;
  r = arsum_bytes1(d, n);
}

void arsum_bytes2_harness()
{
  uint8_t *d;
  uint32_t r;
  size_t n;
  r = arsum_bytes2(d, n);
}

void arsum_swords_harness()
{
  int32_t *d;
  int32_t r;
  int32_t n;
  r = arsum_swords(d, n);
}

void assign_st1_harness()
{
  st source;
  st dest;

  assign_st1(dest, source);
}

void assign_st2_harness()
{
  st source;
  st dest;

  assign_st2(dest, source);
}

void assign_st3_harness()
{
  st source;
  st dest;

  assign_st3(dest, source);
}

void init_st_harness()
{
  st dest;

  init_st(dest);
}

void zero_slice_harness()
{
  uint8_t *dst;
  size_t len;

  zero_slice(dst, len);
}

void zero_array_ts_harness()
{
  uint8_t *dst;
  unsigned len;

  zero_array_ts(dst, len);
}

void zero_array_correct_harness()
{
  uint8_t *dst;
  unsigned len;

  zero_array_correct(dst, len);
}

void constant_time_equals_strict_harness()
{
  uint8_t *a;
  uint8_t *b;
  uint32_t len;
  bool result;
  result = constant_time_equals_strict(a, b, len);
}

void constant_time_equals_total_harness()
{
  uint8_t *a;
  uint8_t *b;
  uint32_t len;
  bool result;
  result = constant_time_equals_total(a, b, len);
}

void ctcc_harness()
{
  uint8_t *a;
  uint8_t *b;
  uint32_t len;
  uint8_t dont;
  int result;

  result = ctcc(a, b, len, dont);
}

void ctunpad_harness()
{
  uint8_t *src;
  uint8_t *dst;
  uint32_t srclen;
  uint32_t dstlen;
  int result;
  result = ctunpad(dst, src, srclen, dstlen);
}

void inc_vector_harness()
{
  int32_t *v;
  inc_vector(v);
}

void inc_matrix_harness()
{
  int32_t *m;
  inc_matrix(m);
}

void condmod_harness()
{
  int16_t *v;
  int r;
  r = condmod(v);
}
