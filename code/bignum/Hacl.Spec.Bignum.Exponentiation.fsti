module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module BN = Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_mod_exp_pre
  (#t:limb_t)
  (#len:BN.bn_len t)
  (n:lbignum t len)
  (a:lbignum t len)
  (bBits:size_nat)
  (b:lbignum t (blocks0 bBits (bits t)))
 =
   bn_v n % 2 = 1 /\ 1 < bn_v n /\
   bn_v b < pow2 bBits /\ bn_v a < bn_v n


let bn_mod_exp_post
  (#t:limb_t)
  (#len:BN.bn_len t)
  (n:lbignum t len)
  (a:lbignum t len)
  (bBits:size_nat)
  (b:lbignum t (blocks0 bBits (bits t)))
  (res:lbignum t len)
 =
  bn_mod_exp_pre n a bBits b /\
  bn_v res == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b)


val bn_check_mod_exp:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_nat
  -> b:lbignum t (blocks0 bBits (bits t)) ->
  res:limb t{
    let b =
      bn_v n % 2 = 1 && 1 < bn_v n &&
      bn_v b < pow2 bBits &&
      bn_v a < bn_v n in
    v res == (if b then v (ones t SEC) else v (zeros t SEC))}


let bn_mod_exp_precomp_st (t:limb_t) (len:BN.bn_len t) =
    n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> a:lbignum t len
  -> bBits:size_nat
  -> b:lbignum t (blocks0 bBits (bits t)) ->
  Pure (lbignum t len)
  (requires
    bn_mod_exp_pre n a bBits b /\
    bn_v r2 == pow2 (2 * bits t * len) % bn_v n /\
    (1 + bn_v n * v mu) % pow2 (bits t) == 0)
  (ensures fun res ->
    bn_mod_exp_post n a bBits b res)


val bn_mod_exp_rl_precomp: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_precomp_st t len
val bn_mod_exp_mont_ladder_swap_precomp: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_precomp_st t len

val bn_mod_exp_fw_precomp:
    #t:limb_t
  -> len:BN.bn_len t
  -> l:size_pos{l < bits t /\ pow2 l * len <= max_size_t} ->
  bn_mod_exp_precomp_st t len


//no need to distinguish between vartime and consttime in the spec
val bn_mod_exp_vartime_precomp: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_precomp_st t len
val bn_mod_exp_consttime_precomp: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_precomp_st t len


let bn_mod_exp_precompr2_st (t:limb_t) (len:BN.bn_len t) =
    n:lbignum t len
  -> r2:lbignum t len
  -> a:lbignum t len
  -> bBits:size_nat
  -> b:lbignum t (blocks0 bBits (bits t)) ->
  Pure (lbignum t len)
  (requires
    bn_mod_exp_pre n a bBits b /\
    bn_v r2 == pow2 (2 * bits t * len) % bn_v n)
  (ensures fun res ->
    bn_mod_exp_post n a bBits b res)


val bn_mod_exp_vartime_precompr2: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_precompr2_st t len
val bn_mod_exp_consttime_precompr2: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_precompr2_st t len


let bn_mod_exp_st (t:limb_t) (len:BN.bn_len t) =
    nBits:size_nat
  -> n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_nat
  -> b:lbignum t (blocks0 bBits (bits t)) ->
  Pure (lbignum t len)
  (requires
    bn_mod_exp_pre n a bBits b /\
    nBits / bits t < len /\ pow2 nBits < bn_v n)
  (ensures  fun res ->
    bn_mod_exp_post n a bBits b res)

val bn_mod_exp_vartime: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_st t len
val bn_mod_exp_consttime: #t:limb_t -> len:BN.bn_len t -> bn_mod_exp_st t len
