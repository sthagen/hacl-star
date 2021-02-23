module Hacl.RSAPSS2048_SHA256

open FStar.Mul
open Lib.IntTypes

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module RI = Hacl.Impl.RSAPSS
module RK = Hacl.Impl.RSAPSS.Keys

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BD = Hacl.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
let add: BN.bn_add_eq_len_st t_limbs n_limbs =
  BN.bn_add_eq_len n_limbs

[@CInline]
let sub: BN.bn_sub_eq_len_st t_limbs n_limbs =
  BN.bn_sub_eq_len n_limbs

[@CInline]
let add_mod_n: BN.bn_add_mod_n_st t_limbs n_limbs =
  BN.bn_add_mod_n n_limbs

[@CInline]
let mul (a:BD.lbignum t_limbs n_limbs) : BN.bn_karatsuba_mul_st t_limbs n_limbs a =
  BN.bn_karatsuba_mul n_limbs a

[@CInline]
let sqr (a:BD.lbignum t_limbs n_limbs) : BN.bn_karatsuba_sqr_st t_limbs n_limbs a =
  BN.bn_karatsuba_sqr n_limbs a

inline_for_extraction noextract
instance bn_inst: BN.bn t_limbs = {
  BN.len = n_limbs;
  BN.add;
  BN.sub;
  BN.add_mod_n;
  BN.mul;
  BN.sqr
}

[@CInline]
let mont_check: BM.bn_check_modulus_st t_limbs n_limbs =
  BM.bn_check_modulus

[@CInline]
let precomp: BM.bn_precomp_r2_mod_n_st t_limbs n_limbs =
  BM.bn_precomp_r2_mod_n bn_inst

[@CInline]
let reduction: BM.bn_mont_reduction_st t_limbs n_limbs =
  BM.bn_mont_reduction bn_inst

[@CInline]
let to: BM.bn_to_mont_st t_limbs n_limbs =
  BM.bn_to_mont bn_inst reduction

[@CInline]
let from: BM.bn_from_mont_st t_limbs n_limbs =
  BM.bn_from_mont bn_inst reduction

[@CInline]
let mont_mul: BM.bn_mont_mul_st t_limbs n_limbs =
  BM.bn_mont_mul bn_inst reduction

[@CInline]
let mont_sqr: BM.bn_mont_sqr_st t_limbs n_limbs =
  BM.bn_mont_sqr bn_inst reduction

inline_for_extraction noextract
instance mont_inst: BM.mont t_limbs = {
  BM.bn = bn_inst;
  BM.mont_check;
  BM.precomp;
  BM.reduction;
  BM.to;
  BM.from;
  BM.mul = mont_mul;
  BM.sqr = mont_sqr;
}

[@CInline]
let exp_check: BE.bn_check_mod_exp_st t_limbs n_limbs =
  BE.bn_check_mod_exp mont_inst

[@CInline]
let mod_exp_raw_precompr2: BE.bn_mod_exp_raw_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_raw_precompr2 mont_inst

[@CInline]
let mod_exp_ct_precompr2: BE.bn_mod_exp_ct_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_ct_precompr2 mont_inst

[@CInline]
let mod_exp_fw_raw_precompr2: BE.bn_mod_exp_fw_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_fw_raw_precompr2 mont_inst

[@CInline]
let mod_exp_fw_ct_precompr2: BE.bn_mod_exp_fw_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_fw_ct_precompr2 mont_inst

inline_for_extraction noextract
instance ke_2048: BE.exp t_limbs = {
  BE.mont = mont_inst;
  BE.exp_check;
  BE.raw_mod_exp_precomp = mod_exp_raw_precompr2;
  BE.ct_mod_exp_precomp = mod_exp_ct_precompr2;
  BE.raw_mod_exp_fw_precomp = mod_exp_fw_raw_precompr2;
  BE.ct_mod_exp_fw_precomp = mod_exp_fw_ct_precompr2;
}


private
[@CInline]
let load_pkey : RK.rsapss_load_pkey_st t_limbs ke_2048 modBits =
  RK.rsapss_load_pkey ke_2048 modBits RK.mk_runtime_rsapss_checks

private
[@CInline]
let load_skey : RK.rsapss_load_skey_st t_limbs ke_2048 modBits =
  RK.rsapss_load_skey ke_2048 modBits RK.mk_runtime_rsapss_checks load_pkey


let rsapss_sign eBits dBits skey sLen salt msgLen msg sgnt =
  RI.rsapss_sign ke_2048 a_hash modBits eBits dBits skey sLen salt msgLen msg sgnt


let rsapss_verify eBits pkey sLen k sgnt msgLen msg =
  RI.rsapss_verify ke_2048 a_hash modBits eBits pkey sLen k sgnt msgLen msg


let new_rsapss_load_pkey r eBits nb eb =
  RK.new_rsapss_load_pkey ke_2048 modBits load_pkey r eBits nb eb


let new_rsapss_load_skey r eBits dBits nb eb db =
  RK.new_rsapss_load_skey ke_2048 modBits load_skey r eBits dBits nb eb db


let rsapss_skey_sign eBits dBits nb eb db sLen salt msgLen msg sgnt =
  RI.rsapss_skey_sign ke_2048 a_hash modBits load_skey rsapss_sign eBits dBits nb eb db sLen salt msgLen msg sgnt


let rsapss_pkey_verify eBits nb eb sLen k sgnt msgLen msg =
  RI.rsapss_pkey_verify ke_2048 a_hash modBits load_pkey rsapss_verify eBits nb eb sLen k sgnt msgLen msg
