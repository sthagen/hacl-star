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


#ifndef __Hacl_Bignum_H
#define __Hacl_Bignum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "lib_intrinsics.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"

static inline void
Hacl_Bignum_Convert_bn_from_bytes_be_uint64(uint32_t len, uint8_t *b, uint64_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint64_t *os = res;
    uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;
  }
}

static inline void
Hacl_Bignum_Convert_bn_to_bytes_be_uint64(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  uint32_t numb = (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * numb, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
}

static inline uint64_t
Hacl_Bignum_Base_mul_wide_add_u64(uint64_t a, uint64_t b, uint64_t c_in, uint64_t *out)
{
  FStar_UInt128_uint128
  res = FStar_UInt128_add(FStar_UInt128_mul_wide(a, b), FStar_UInt128_uint64_to_uint128(c_in));
  out[0U] = FStar_UInt128_uint128_to_uint64(res);
  return FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, (uint32_t)64U));
}

static inline uint64_t
Hacl_Bignum_Base_mul_wide_add2_u64(uint64_t a, uint64_t b, uint64_t c_in, uint64_t *out)
{
  uint64_t out0 = out[0U];
  FStar_UInt128_uint128
  res =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(a, b),
        FStar_UInt128_uint64_to_uint128(c_in)),
      FStar_UInt128_uint64_to_uint128(out0));
  out[0U] = FStar_UInt128_uint128_to_uint64(res);
  return FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, (uint32_t)64U));
}

static inline uint64_t Hacl_Bignum_Lib_bn_get_top_index_u64(uint32_t len, uint64_t *b)
{
  uint64_t priv = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t mask = FStar_UInt64_eq_mask(b[i], (uint64_t)0U);
    priv = (mask & priv) | (~mask & (uint64_t)i);
  }
  return priv;
}

static inline uint64_t
Hacl_Bignum_Addition_bn_sub_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  return c;
}

static inline uint64_t
Hacl_Bignum_Addition_bn_add_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  return c;
}

static inline void
Hacl_Bignum_Multiplication_bn_mul_u64(
  uint32_t aLen,
  uint64_t *a,
  uint32_t bLen,
  uint64_t *b,
  uint64_t *res
)
{
  uint32_t resLen = aLen + bLen;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < bLen; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
    for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    res[aLen + i0] = r;
  }
}

static inline void
Hacl_Bignum_Multiplication_bn_sqr_u64(uint32_t aLen, uint64_t *a, uint64_t *res)
{
  uint32_t resLen = aLen + aLen;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < aLen; i0++)
  {
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t a_i = ab[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    res[i0 + i0] = r;
  }
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, res, res, res);
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  uint64_t tmp[resLen];
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, res, tmp, res);
}

static inline void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    Hacl_Bignum_Multiplication_bn_mul_u64(aLen, a, aLen, b, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *b0 = b;
  uint64_t *b1 = b + len2;
  uint64_t *t0 = tmp;
  uint64_t *t1 = tmp + len2;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c10 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c00 = c0;
  uint64_t c010 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b0, b1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b1, b0, t1);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t1;
    uint64_t x = (((uint64_t)0U - c010) & t1[i]) | (~((uint64_t)0U - c010) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c11 = c010;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, t0, t1, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a0, b0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a1, b1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t *t67 = tmp + (uint32_t)3U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c_sign = c00 ^ c11;
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t67);
  uint64_t c31 = c2 - c3;
  uint64_t c4 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c41 = c2 + c4;
  uint64_t mask = (uint64_t)0U - c_sign;
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    uint64_t *os = t45;
    uint64_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint64_t c5 = (mask & c41) | (~mask & c31);
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c6 = r10;
  uint64_t c60 = c6;
  uint64_t c7 = c5 + c60;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t11 = a11[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i0);
      uint64_t t110 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t110, (uint64_t)0U, res_i1);
      uint64_t t111 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t111, (uint64_t)0U, res_i2);
      uint64_t t112 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t112, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t11 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i);
    }
    uint64_t c110 = c;
    r1 = c110;
  }
  else
  {
    r1 = c01;
  }
  uint64_t c8 = r1;
  uint64_t c = c8;
  uint64_t c9 = c;
}

static inline void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    Hacl_Bignum_Multiplication_bn_sqr_u64(aLen, a, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *t0 = tmp;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c00 = c0;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, t0, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c5 = c2 - c3;
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c4 = r10;
  uint64_t c6 = c4;
  uint64_t c7 = c5 + c6;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a11[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    r1 = c10;
  }
  else
  {
    r1 = c01;
  }
  uint64_t c8 = r1;
  uint64_t c = c8;
  uint64_t c9 = c;
}

static inline void
Hacl_Bignum_bn_add_mod_n_u64(
  uint32_t len1,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t tmp[len1];
  memset(tmp, 0U, len1 * sizeof (uint64_t));
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline uint64_t Hacl_Bignum_ModInvLimb_mod_inv_uint64(uint64_t n0)
{
  uint64_t alpha = (uint64_t)9223372036854775808U;
  uint64_t beta = n0;
  uint64_t ub = (uint64_t)0U;
  uint64_t vb = (uint64_t)0U;
  ub = (uint64_t)1U;
  vb = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t us = ub;
    uint64_t vs = vb;
    uint64_t u_is_odd = (uint64_t)0U - (us & (uint64_t)1U);
    uint64_t beta_if_u_is_odd = beta & u_is_odd;
    ub = ((us ^ beta_if_u_is_odd) >> (uint32_t)1U) + (us & beta_if_u_is_odd);
    uint64_t alpha_if_u_is_odd = alpha & u_is_odd;
    vb = (vs >> (uint32_t)1U) + alpha_if_u_is_odd;
  }
  return vb;
}

static inline void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *res
)
{
  memset(res, 0U, len * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res[i] = res[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)128U * len - nBits; i0++)
  {
    Hacl_Bignum_bn_add_mod_n_u64(len, n, res, res, res);
  }
}

static inline void
Hacl_Bignum_Montgomery_bn_mont_reduction_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *c,
  uint64_t *res
)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
    for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + len + i0;
    uint64_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uint64_t c01 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = c01 - c10;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void
Hacl_Bignum_Montgomery_bn_mont_mul_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, aM, bM, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

static inline void
Hacl_Bignum_Montgomery_bn_mont_sqr_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, aM, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

static inline void
Hacl_Bignum_Exponentiation_bn_mod_exp_raw_precompr2_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t aM[len];
  memset(aM, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t accM[len];
  memset(accM, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c0[len + len];
  memset(c0, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp0[(uint32_t)4U * len];
  memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp0, c0);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv, c0, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t one[len];
  memset(one, 0U, len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp1[(uint32_t)4U * len];
  memset(tmp1, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, one, r2, tmp1, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv, c, accM);
  for (uint32_t i = (uint32_t)0U; i < bBits; i++)
  {
    uint32_t i1 = i / (uint32_t)64U;
    uint32_t j = i % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    if (!(bit == (uint64_t)0U))
    {
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len, n, nInv, accM, aM, accM);
    }
    Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len, n, nInv, aM, aM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t tmp[len + len];
  memset(tmp, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp, accM, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv, tmp, res);
}

static inline void
Hacl_Bignum_Exponentiation_bn_mod_exp_fw_ct_precompr2_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint32_t l,
  uint64_t *r2,
  uint64_t *res
)
{
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t aM[len];
  memset(aM, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t accM[len];
  memset(accM, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c0[len + len];
  memset(c0, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp0[(uint32_t)4U * len];
  memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp0, c0);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv, c0, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t one[len];
  memset(one, 0U, len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c2[len + len];
  memset(c2, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, one, r2, tmp, c2);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv, c2, accM);
  uint32_t table_len = (uint32_t)1U << l;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * len);
  uint64_t table[table_len * len];
  memset(table, 0U, table_len * len * sizeof (uint64_t));
  memcpy(table, accM, len * sizeof (uint64_t));
  uint64_t *t1 = table + len;
  memcpy(t1, aM, len * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * len;
    uint64_t *t2 = table + (i + (uint32_t)2U) * len;
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len, n, nInv, t11, aM, t2);
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / l; i0++)
  {
    uint64_t mask_l = ((uint64_t)1U << l) - (uint64_t)1U;
    uint32_t i1 = (bBits - l * i0 - l) / (uint32_t)64U;
    uint32_t j = (bBits - l * i0 - l) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t a_bits_l[len];
    memset(a_bits_l, 0U, len * sizeof (uint64_t));
    memcpy(a_bits_l, table, len * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < table_len - (uint32_t)1U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * len;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    for (uint32_t i = (uint32_t)0U; i < l; i++)
    {
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len, n, nInv, accM, accM);
    }
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len, n, nInv, accM, a_bits_l, accM);
  }
  if (!(bBits % l == (uint32_t)0U))
  {
    uint32_t c = bBits % l;
    uint32_t c10 = bBits % l;
    uint64_t mask_l = ((uint64_t)1U << c10) - (uint64_t)1U;
    uint32_t i0 = (uint32_t)0U;
    uint32_t j = (uint32_t)0U;
    uint64_t p1 = b[i0] >> j;
    uint64_t ite;
    if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    uint64_t bits_c0 = bits_c;
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t a_bits_c[len];
    memset(a_bits_c, 0U, len * sizeof (uint64_t));
    memcpy(a_bits_c, table, len * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < table_len - (uint32_t)1U; i1++)
    {
      uint64_t c1 = FStar_UInt64_eq_mask(bits_c0, (uint64_t)(i1 + (uint32_t)1U));
      uint64_t *res_j = table + (i1 + (uint32_t)1U) * len;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint64_t *os = a_bits_c;
        uint64_t x = (c1 & res_j[i]) | (~c1 & a_bits_c[i]);
        os[i] = x;
      }
    }
    for (uint32_t i = (uint32_t)0U; i < c; i++)
    {
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len, n, nInv, accM, accM);
    }
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(len, n, nInv, accM, a_bits_c, accM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t tmp1[len + len];
  memset(tmp1, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp1, accM, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv, tmp1, res);
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum_H_DEFINED
#endif
