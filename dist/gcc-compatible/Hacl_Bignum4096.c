/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_Bignum4096.h"

/*******************************************************************************

A verified 4096-bit bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of four unsigned 64-bit integers, i.e. uint64_t[64]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint64_t sixteen[64] = { 0x10 }

  (relying on the fact that when an initializer-list is provided, the remainder
  of the object gets initialized as if it had static storage duration, i.e. with
  zeroes)

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 32-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/*
Write `a + b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum4096_add(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  return c;
}

/*
Write `a - b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum4096_sub(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  return c;
}

static inline void add_mod_n(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128].
*/
void Hacl_Bignum4096_mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = (uint32_t)128U;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t a_i = a[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    res[(uint32_t)64U + i0] = r;
  }
}

static inline uint64_t mont_check(uint64_t *n)
{
  uint64_t one[64U] = { 0U };
  memset(one, 0U, (uint32_t)64U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t bit0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bit0;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc;
  return m0 & m1;
}

static inline void precomp(uint32_t nBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, (uint32_t)64U * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res[i] = res[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)8192U - nBits; i0++)
  {
    add_mod_n(n, res, res, res);
  }
}

static inline void reduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t a_i = n[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + (uint32_t)64U + i0;
    uint64_t res_j = c[(uint32_t)64U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + (uint32_t)64U, (uint32_t)64U * sizeof (uint64_t));
  uint64_t c01 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = c01 - c10;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void
mont_mul(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *bM, uint64_t *resM)
{
  uint64_t c[128U] = { 0U };
  uint32_t resLen = (uint32_t)128U;
  memset(c, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t bj = bM[i0];
    uint64_t *res_j = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t a_i = aM[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i0);
      uint64_t a_i0 = aM[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c1, res_i1);
      uint64_t a_i1 = aM[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c1, res_i2);
      uint64_t a_i2 = aM[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
    {
      uint64_t a_i = aM[i];
      uint64_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i);
    }
    uint64_t r = c1;
    c[(uint32_t)64U + i0] = r;
  }
  reduction(n, nInv_u64, c, resM);
}

static inline void mont_sqr(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *resM)
{
  uint64_t c[128U] = { 0U };
  uint32_t resLen = (uint32_t)128U;
  memset(c, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t bj = aM[i0];
    uint64_t *res_j = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t a_i = aM[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i0);
      uint64_t a_i0 = aM[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c1, res_i1);
      uint64_t a_i1 = aM[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c1, res_i2);
      uint64_t a_i2 = aM[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
    {
      uint64_t a_i = aM[i];
      uint64_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i);
    }
    uint64_t r = c1;
    c[(uint32_t)64U + i0] = r;
  }
  reduction(n, nInv_u64, c, resM);
}

/*
Write `a mod n` in `res` if a < n * n.

  The argument a is meant to be a 8192-bit bignum, i.e. uint64_t[128].
  The argument n, r2 and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument r2 is a precomputed constant 2 ^ 8192 mod n obtained through Hacl_Bignum4096_new_precompr2.

  This function is *UNSAFE* and requires C clients to observe the precondition
  of bn_mod_slow_precompr2_lemma in Hacl.Spec.Bignum.ModReduction.fst, which
  amounts to:
  • 1 < n
  • n % 2 = 1
  • a < n * n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod below.
*/
void Hacl_Bignum4096_mod_precompr2(uint64_t *n, uint64_t *a, uint64_t *r2, uint64_t *res)
{
  uint64_t a_mod[64U] = { 0U };
  uint64_t a1[128U] = { 0U };
  memcpy(a1, a, (uint32_t)128U * sizeof (uint64_t));
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t qj = mu * a1[i0];
    uint64_t *res_j0 = a1 + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t a_i = n[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c, res_i);
    }
    for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i);
    }
    uint64_t r = c;
    uint64_t c1 = r;
    uint64_t *resb = a1 + (uint32_t)64U + i0;
    uint64_t res_j = a1[(uint32_t)64U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c1, res_j, resb);
  }
  memcpy(a_mod, a1 + (uint32_t)64U, (uint32_t)64U * sizeof (uint64_t));
  uint64_t c01 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t t1 = a_mod[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = a_mod[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = a_mod[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = a_mod[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)64U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a_mod[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c01 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = a_mod;
    uint64_t x = (c2 & a_mod[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
  uint64_t c3[128U] = { 0U };
  Hacl_Bignum4096_mul(a_mod, r2, c3);
  reduction(n, mu, c3, res);
}

/*
Write `a mod n` in `res` if a < n * n.

  The argument a is meant to be a 8192-bit bignum, i.e. uint64_t[128].
  The argument n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  The function returns false if any of the preconditions of mod_precompr2 above
  are violated, true otherwise.
*/
bool Hacl_Bignum4096_mod(uint64_t *n, uint64_t *a, uint64_t *res)
{
  uint64_t m0 = mont_check(n);
  uint64_t n2[128U] = { 0U };
  Hacl_Bignum4096_mul(n, n, n2);
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)128U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n2[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n2[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc;
  uint64_t is_valid_m = m0 & m1;
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)64U, n);
  uint64_t r2[64U] = { 0U };
  precomp(nBits, n, r2);
  Hacl_Bignum4096_mod_precompr2(n, a, r2, res);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = res[i];
    uint64_t x0 = is_valid_m & x;
    os[i] = x0;
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

static inline uint64_t exp_check(uint64_t *n, uint64_t *a, uint32_t bBits, uint64_t *b)
{
  uint64_t m0 = mont_check(n);
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
  uint64_t bn_zero[bLen];
  memset(bn_zero, 0U, bLen * sizeof (uint64_t));
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  for (uint32_t i = (uint32_t)0U; i < bLen; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(b[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  uint64_t res = mask1;
  uint64_t m1 = res;
  uint64_t m1_ = ~m1;
  uint64_t m2;
  if (bBits < (uint32_t)64U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
    uint64_t b2[bLen];
    memset(b2, 0U, bLen * sizeof (uint64_t));
    uint32_t i0 = bBits / (uint32_t)64U;
    uint32_t j = bBits % (uint32_t)64U;
    b2[i0] = b2[i0] | (uint64_t)1U << j;
    uint64_t acc = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < bLen; i++)
    {
      uint64_t beq = FStar_UInt64_eq_mask(b[i], b2[i]);
      uint64_t blt = ~FStar_UInt64_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
    }
    uint64_t res0 = acc;
    m2 = res0;
  }
  else
  {
    m2 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  }
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m3 = acc;
  uint64_t m = (m1_ & m2) & m3;
  return m0 & m;
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument r2 is a precomputed constant 2 ^ 8192 mod n obtained through Hacl_Bignum4096_new_precompr2.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_ct_* functions for constant-time variants.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp_raw below.
*/
void
Hacl_Bignum4096_mod_exp_raw_precompr2(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  uint64_t aM[64U] = { 0U };
  uint64_t accM[64U] = { 0U };
  uint64_t c0[128U] = { 0U };
  Hacl_Bignum4096_mul(a, r2, c0);
  reduction(n, nInv, c0, aM);
  uint64_t one[64U] = { 0U };
  memset(one, 0U, (uint32_t)64U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t c[128U] = { 0U };
  Hacl_Bignum4096_mul(one, r2, c);
  reduction(n, nInv, c, accM);
  for (uint32_t i = (uint32_t)0U; i < bBits; i++)
  {
    uint32_t i1 = i / (uint32_t)64U;
    uint32_t j = i % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    if (!(bit == (uint64_t)0U))
    {
      mont_mul(n, nInv, accM, aM, accM);
    }
    mont_sqr(n, nInv, aM, aM);
  }
  uint64_t tmp[128U] = { 0U };
  memcpy(tmp, accM, (uint32_t)64U * sizeof (uint64_t));
  reduction(n, nInv, tmp, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument r2 is a precomputed constant 2 ^ 8192 mod n obtained through Hacl_Bignum4096_new_precompr2.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_raw_precompr2.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp_ct below.
*/
void
Hacl_Bignum4096_mod_exp_ct_precompr2(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  uint64_t aM[64U] = { 0U };
  uint64_t accM[64U] = { 0U };
  uint64_t c0[128U] = { 0U };
  Hacl_Bignum4096_mul(a, r2, c0);
  reduction(n, nInv, c0, aM);
  uint64_t one[64U] = { 0U };
  memset(one, 0U, (uint32_t)64U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t c[128U] = { 0U };
  Hacl_Bignum4096_mul(one, r2, c);
  reduction(n, nInv, c, accM);
  uint64_t sw = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
  {
    uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
    uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    uint64_t sw1 = bit ^ sw;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw1) & (accM[i] ^ aM[i]);
      accM[i] = accM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    mont_mul(n, nInv, aM, accM, aM);
    mont_sqr(n, nInv, accM, accM);
    sw = bit;
  }
  uint64_t sw0 = sw;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t dummy = ((uint64_t)0U - sw0) & (accM[i] ^ aM[i]);
    accM[i] = accM[i] ^ dummy;
    aM[i] = aM[i] ^ dummy;
  }
  uint64_t tmp[128U] = { 0U };
  memcpy(tmp, accM, (uint32_t)64U * sizeof (uint64_t));
  reduction(n, nInv, tmp, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_ct_* functions for constant-time variants.

  The function returns false if any of the preconditions of mod_exp_precompr2 are
  violated, true otherwise.
*/
bool
Hacl_Bignum4096_mod_exp_raw(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)64U, n);
  if (is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    uint64_t r2[64U] = { 0U };
    precomp(nBits, n, r2);
    Hacl_Bignum4096_mod_exp_raw_precompr2(n, a, bBits, b, r2, res);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = res[i];
    uint64_t x0 = is_valid_m & x;
    os[i] = x0;
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp.

  The function returns false if any of the preconditions of
  mod_exp_ct_precompr2 are violated, true otherwise.
*/
bool
Hacl_Bignum4096_mod_exp_ct(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)64U, n);
  if (is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    uint64_t r2[64U] = { 0U };
    precomp(nBits, n, r2);
    Hacl_Bignum4096_mod_exp_ct_precompr2(n, a, bBits, b, r2, res);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = res[i];
    uint64_t x0 = is_valid_m & x;
    os[i] = x0;
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

/*
Compute `2 ^ 8192 mod n`.

  The argument n points to a 4096-bit bignum of valid memory.
  The function returns a heap-allocated 4096-bit bignum, or NULL if:
  • the allocation failed, or
  • n % 2 = 1 && 1 < n does not hold

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum4096_new_precompr2(uint64_t *n)
{
  uint64_t one[64U] = { 0U };
  memset(one, 0U, (uint32_t)64U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t bit0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bit0;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc;
  uint64_t is_valid_m = m0 & m1;
  if (!(is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU))
  {
    return NULL;
  }
  uint64_t *res = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)64U, n);
  memset(res2, 0U, (uint32_t)64U * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res2[i] = res2[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)8192U - nBits; i0++)
  {
    add_mod_n(n, res2, res2, res2);
  }
  return res2;
}

/*
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  This function is *UNSAFE* and requires C clients to observe bn_mod_inv_prime_pre
  from Hacl.Spec.Bignum.ModInv.fst, which amounts to:
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n 
*/
bool Hacl_Bignum4096_mod_inv_prime_raw(uint64_t *n, uint64_t *a, uint64_t *res)
{
  uint64_t m0 = mont_check(n);
  uint64_t bn_zero[64U] = { 0U };
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(a[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  uint64_t res10 = mask1;
  uint64_t m1 = res10;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m2 = acc;
  uint64_t is_valid_m = (m0 & ~m1) & m2;
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)64U, n);
  if (is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    uint64_t n2[64U] = { 0U };
    uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, n[0U], (uint64_t)2U, n2);
    uint64_t c1;
    if ((uint32_t)1U < (uint32_t)64U)
    {
      uint32_t rLen = (uint32_t)63U;
      uint64_t *a1 = n + (uint32_t)1U;
      uint64_t *res1 = n2 + (uint32_t)1U;
      uint64_t c = c0;
      for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
      {
        uint64_t t1 = a1[(uint32_t)4U * i];
        uint64_t *res_i0 = res1 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i0);
        uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, (uint64_t)0U, res_i1);
        uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, (uint64_t)0U, res_i2);
        uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, (uint64_t)0U, res_i);
      }
      for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
      {
        uint64_t t1 = a1[i];
        uint64_t *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i);
      }
      uint64_t c10 = c;
      c1 = c10;
    }
    else
    {
      c1 = c0;
    }
    uint64_t r2[64U] = { 0U };
    precomp(nBits, n, r2);
    Hacl_Bignum4096_mod_exp_raw_precompr2(n, a, (uint32_t)4096U, n2, r2, res);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = res[i];
    uint64_t x0 = is_valid_m & x;
    os[i] = x0;
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}


/********************/
/* Loads and stores */
/********************/


/*
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum4096_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U <= (uint32_t)536870911U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U);
  uint64_t
  *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint64_t *os = res2;
    uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;
  }
  return res2;
}

/*
Serialize a bignum into big-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory.
*/
void Hacl_Bignum4096_bn_to_bytes_be(uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  uint32_t numb = (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * numb, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - (uint32_t)512U, (uint32_t)512U * sizeof (uint8_t));
}


/***************/
/* Comparisons */
/***************/


/*
Returns 2 ^ 64 - 1 if and only if argument a is strictly less than the argument b, otherwise returns 0.
*/
uint64_t Hacl_Bignum4096_lt_mask(uint64_t *a, uint64_t *b)
{
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], b[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  return acc;
}

