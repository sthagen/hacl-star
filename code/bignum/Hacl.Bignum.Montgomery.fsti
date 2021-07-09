module Hacl.Bignum.Montgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Bignum

include Hacl.Bignum.ModInvLimb

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
let bn_check_modulus_st (t:limb_t) (len:BN.meta_len t) =
  n:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h n)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_modulus (as_seq h0 n))


inline_for_extraction noextract
val bn_check_modulus: #t:limb_t -> #len:BN.meta_len t -> bn_check_modulus_st t len


inline_for_extraction noextract
let bn_precomp_r2_mod_n_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t{v nBits / bits t < v len}
  -> n:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h res /\ disjoint n res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_precomp_r2_mod_n (v nBits) (as_seq h0 n))


inline_for_extraction noextract
val bn_precomp_r2_mod_n: #t:limb_t -> k:BN.bn t -> bn_precomp_r2_mod_n_st t k.BN.len


inline_for_extraction noextract
let bn_mont_precomp_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t
  -> n:lbignum t len
  -> r2:lbignum t len ->
  Stack (limb t)
  (requires fun h ->
    live h n /\ live h r2 /\ disjoint n r2 /\

    1 < bn_v h n /\ bn_v h n % 2 = 1 /\
    pow2 (v nBits) < bn_v h n /\ v nBits / bits t < v len)
  (ensures  fun h0 mu h1 -> modifies (loc r2) h0 h1 /\
    (as_seq h1 r2, mu) == S.bn_mont_precomp (v nBits) (as_seq h0 n))


inline_for_extraction noextract
val bn_mont_precomp:
    #t:limb_t
  -> len:BN.meta_len t
  -> precompr2:bn_precomp_r2_mod_n_st t len ->
  bn_mont_precomp_st t len


inline_for_extraction noextract
let bn_mont_reduction_st (t:limb_t) (len:size_t{0 < v len /\ v len + v len <= max_size_t}) =
    n:lbignum t len
  -> mu:limb t
  -> c:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    as_seq h1 res == S.bn_mont_reduction (as_seq h0 n) mu (as_seq h0 c))


inline_for_extraction noextract
val bn_mont_reduction: #t:limb_t -> k:BN.bn t -> bn_mont_reduction_st t k.BN.len


inline_for_extraction noextract
let bn_to_mont_st (t:limb_t) (nLen:BN.meta_len t) =
    n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t nLen
  -> aM:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h a /\ live h aM /\
    disjoint a r2 /\ disjoint a n /\ disjoint a aM /\
    disjoint n r2 /\ disjoint n aM /\ disjoint r2 aM)
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    as_seq h1 aM == S.bn_to_mont (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a))


inline_for_extraction noextract
val bn_to_mont: #t:limb_t -> k:BN.bn t -> mr:bn_mont_reduction_st t k.BN.len -> bn_to_mont_st t k.BN.len


inline_for_extraction noextract
let bn_from_mont_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> a:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    disjoint aM a /\ disjoint aM n /\ disjoint a n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_seq h1 a == S.bn_from_mont (as_seq h0 n) mu (as_seq h0 aM))


// This one just needs a specialized implementation of mont_reduction. No point
// in doing a type class for a single function , so we take it as a parameter.
inline_for_extraction noextract
val bn_from_mont: #t:limb_t -> k:BN.bn t -> mr:bn_mont_reduction_st t k.BN.len -> bn_from_mont_st t k.BN.len


inline_for_extraction noextract
let bn_mont_mul_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> bM:lbignum t len
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h bM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM bM /\
    eq_or_disjoint aM resM /\ eq_or_disjoint bM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.bn_mont_mul (as_seq h0 n) mu (as_seq h0 aM) (as_seq h0 bM))


/// This one needs both the type class and a specialized montgomery reduction.
inline_for_extraction noextract
val bn_mont_mul: #t:limb_t -> k:BN.bn t -> mr:bn_mont_reduction_st t k.BN.len -> bn_mont_mul_st t k.BN.len


inline_for_extraction noextract
let bn_mont_sqr_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.bn_mont_sqr (as_seq h0 n) mu (as_seq h0 aM))


/// This one needs both the type class and a specialized montgomery reduction.
inline_for_extraction noextract
val bn_mont_sqr: #t:limb_t -> k:BN.bn t -> mr:bn_mont_reduction_st t k.BN.len -> bn_mont_sqr_st t k.BN.len


inline_for_extraction noextract
class mont (t:limb_t) = {
  bn: BN.bn t;
  mont_check: bn_check_modulus_st t bn.BN.len;
  precomp: bn_precomp_r2_mod_n_st t bn.BN.len;
  reduction: bn_mont_reduction_st t bn.BN.len;
  to: bn_to_mont_st t bn.BN.len;
  from: bn_from_mont_st t bn.BN.len;
  mul: bn_mont_mul_st t bn.BN.len;
  sqr: bn_mont_sqr_st t bn.BN.len;
}

/// Encoding type-class hierarchies via a hook for type class resolution.
inline_for_extraction noextract
instance bn_of_mont (t:limb_t) (x:mont t) : BN.bn t = x.bn

// A completely run-time-only instance where the functions above exist in the C code.
inline_for_extraction noextract
val mk_runtime_mont: #t:limb_t -> len:BN.meta_len t -> mont t

val mk_runtime_mont_len_lemma: #t:limb_t -> len:BN.meta_len t ->
  Lemma ((mk_runtime_mont #t len).bn.BN.len == len) [SMTPat (mk_runtime_mont #t len)]


inline_for_extraction noextract
let bn_mont_one_st (t:limb_t) (nLen:BN.meta_len t) =
    n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> oneM:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h oneM /\
    disjoint n r2 /\ disjoint n oneM /\ disjoint r2 oneM)
  (ensures  fun h0 _ h1 -> modifies (loc oneM) h0 h1 /\
    as_seq h1 oneM == S.bn_mont_one (as_seq h0 n) mu (as_seq h0 r2))


inline_for_extraction noextract
val bn_mont_one:
    #t:limb_t
  -> len:BN.meta_len t
  -> bn_mont_from:bn_from_mont_st t len ->
  bn_mont_one_st t len
