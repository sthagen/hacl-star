module Hacl.Bignum.ModInv

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.ModInv

module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BM = Hacl.Bignum.Montgomery
module SD = Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_check_mod_inv_prime_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h n /\ live h a /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_mod_inv_prime (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val bn_check_mod_inv_prime: #t:limb_t -> len:BN.meta_len t -> bn_check_mod_inv_prime_st t len
let bn_check_mod_inv_prime #t len n a =
  let m0 = BM.bn_check_modulus n in
  let m1 = BN.bn_is_zero_mask len a in
  let m2 = BN.bn_lt_mask len a n in
  m0 &. (lognot m1) &. m2


inline_for_extraction noextract
val bn_mod_inv_prime_n2:
    #t:limb_t
  -> len:BN.meta_len t
  -> n:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h -> 1 < bn_v h n /\
    live h n /\ live h res /\ disjoint res n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_inv_prime_n2 (as_seq h0 n))

let bn_mod_inv_prime_n2 #t len n res =
  let c = BN.bn_sub1 len n (uint #t #SEC 2) res in
  ()


inline_for_extraction noextract
let bn_mod_inv_prime_precomp_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> a:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint n a /\
    disjoint res r2 /\ disjoint a r2 /\ disjoint n r2 /\

    S.bn_mod_inv_prime_pre (as_seq h n) (as_seq h a) /\
    bn_v h r2 == pow2 (2 * bits t * v len) % bn_v h n /\
    (1 + bn_v h n * v mu) % pow2 (bits t) == 0)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res * bn_v h0 a % bn_v h0 n = 1)


inline_for_extraction noextract
val mk_bn_mod_inv_prime_precomp:
    #t:limb_t
  -> len:BN.meta_len t
  -> bn_mod_exp_precomp:BE.bn_mod_exp_precomp_st t len ->
  bn_mod_inv_prime_precomp_st t len

let mk_bn_mod_inv_prime_precomp #t len bn_mod_exp_precomp n mu r2 a res =
  let h0 = ST.get () in
  push_frame ();
  let n2 = create len (uint #t #SEC 0) in
  bn_mod_inv_prime_n2 #t len n n2;
  SD.bn_eval_bound (as_seq h0 n) (v len);

  bn_mod_exp_precomp n mu r2 a (size (bits t) *! len) n2 res;
  let h1 = ST.get () in
  assert (bn_v h1 res == Lib.NatMod.pow_mod #(bn_v h0 n) (bn_v h0 a) (bn_v h1 n2));
  S.mod_inv_prime_lemma (bn_v h0 n) (bn_v h0 a);
  pop_frame ()


inline_for_extraction noextract
let bn_mod_inv_prime_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t
  -> n:lbignum t len
  -> a:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint n a /\

    v nBits / bits t < v len /\ pow2 (v nBits) < bn_v h n /\
    S.bn_mod_inv_prime_pre (as_seq h n) (as_seq h a))
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res * bn_v h0 a % bn_v h0 n = 1)


inline_for_extraction noextract
val mk_bn_mod_inv_prime:
    #t:limb_t
  -> len:BN.meta_len t
  -> bn_mod_exp:BE.bn_mod_exp_st t len ->
  bn_mod_inv_prime_st t len

let mk_bn_mod_inv_prime #t len bn_mod_exp nBits n a res =
  let h0 = ST.get () in
  push_frame ();
  let n2 = create len (uint #t #SEC 0) in
  bn_mod_inv_prime_n2 #t len n n2;
  SD.bn_eval_bound (as_seq h0 n) (v len);

  bn_mod_exp nBits n a (size (bits t) *! len) n2 res;
  let h1 = ST.get () in
  assert (bn_v h1 res == Lib.NatMod.pow_mod #(bn_v h0 n) (bn_v h0 a) (bn_v h1 n2));
  S.mod_inv_prime_lemma (bn_v h0 n) (bn_v h0 a);
  pop_frame ()
