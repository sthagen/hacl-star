module Hacl.Impl.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

module S = Lib.Exponentiation
module BD = Hacl.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let inttype_a = t:inttype{t = U32 \/ t = U64}

inline_for_extraction noextract
class lexp_to_exp (a_t:inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) = {
  a_spec: Type0;
  exp: S.exp a_spec;
  linv_ctx: x:LSeq.lseq (uint_t a_t SEC) (v ctx_len) -> Type0;
  linv: x:LSeq.lseq (uint_t a_t SEC) (v len) -> Type0;
  refl: x:LSeq.lseq (uint_t a_t SEC) (v len){linv x} -> GTot a_spec;
}


// inline_for_extraction noextract
// let lone_st
//   (a_t:inttype_a)
//   (len:size_t{v len > 0})
//   (ctx_len:size_t)
//   (to:lexp_to_exp a_t len ctx_len) =
//     ctx:lbuffer (uint_t a_t SEC) ctx_len
//   -> x:lbuffer (uint_t a_t SEC) len ->
//   Stack unit
//   (requires fun h ->
//     live h x /\ live h ctx /\ disjoint ctx x /\
//     to.linv_ctx (as_seq h ctx))
//   (ensures  fun h0 _ h1 -> modifies (loc x) h0 h1 /\
//     to.linv (as_seq h1 x) /\
//     to.refl (as_seq h1 x) == to.exp.S.one)


inline_for_extraction noextract
let lmul_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:lexp_to_exp a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> x:lbuffer (uint_t a_t SEC) len
  -> y:lbuffer (uint_t a_t SEC) len
  -> xy:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h xy /\ live h ctx /\
    eq_or_disjoint x xy /\ eq_or_disjoint y xy /\ eq_or_disjoint x y /\
    disjoint ctx x /\ disjoint ctx y /\ disjoint ctx xy /\
    to.linv (as_seq h x) /\ to.linv (as_seq h y) /\ to.linv_ctx (as_seq h ctx))
  (ensures fun h0 _ h1 -> modifies (loc xy) h0 h1 /\ to.linv (as_seq h1 xy) /\
    to.refl (as_seq h1 xy) == to.exp.S.fmul (refl (as_seq h0 x)) (refl (as_seq h0 y)))


inline_for_extraction noextract
let lsqr_st
  (a_t:inttype_a)
  (len:size_t{v len > 0})
  (ctx_len:size_t)
  (to:lexp_to_exp a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> x:lbuffer (uint_t a_t SEC) len
  -> xx:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h x /\ live h xx /\ live h ctx /\
    disjoint x ctx /\ disjoint xx ctx /\ eq_or_disjoint x xx /\
    to.linv (as_seq h x) /\ to.linv_ctx (as_seq h ctx))
  (ensures fun h0 _ h1 -> modifies (loc xx) h0 h1 /\ to.linv (as_seq h1 xx) /\
    to.refl (as_seq h1 xx) == to.exp.S.fmul (refl (as_seq h0 x)) (refl (as_seq h0 x)))


inline_for_extraction noextract
class lexp (a_t:inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) = {
  to: Ghost.erased (lexp_to_exp a_t len ctx_len);
  //lone: lone_st a_t len ctx_len to;
  lmul: lmul_st a_t len ctx_len to;
  lsqr: lsqr_st a_t len ctx_len to;
}


inline_for_extraction noextract
val lexp_rl:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:lexp a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{0 < v bBits /\ (v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\
    disjoint a acc /\ disjoint b acc /\ disjoint a b /\
    disjoint ctx a /\ disjoint ctx b /\ disjoint ctx acc /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == k.to.exp.S.one)
  (ensures  fun h0 _ h1 -> modifies (loc a |+| loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_rl #k.to.a_spec k.to.exp (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b))


inline_for_extraction noextract
val lexp_mont_ladder_swap:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:lexp a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{0 < v bBits /\ (v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> acc:lbuffer (uint_t a_t SEC) len ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\
    disjoint a acc /\ disjoint b acc /\ disjoint a b /\
    disjoint ctx a /\ disjoint ctx b /\ disjoint ctx acc /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == k.to.exp.S.one)
  (ensures  fun h0 _ h1 -> modifies (loc a |+| loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_mont_ladder_swap #k.to.a_spec k.to.exp (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b))


inline_for_extraction noextract
val lexp_pow_in_place:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:lexp a_t len ctx_len
  -> ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> acc:lbuffer (uint_t a_t SEC) len
  -> b:size_t ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h ctx /\ disjoint acc ctx /\
    k.to.linv (as_seq h acc) /\ k.to.linv_ctx (as_seq h ctx))
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\ k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) == S.exp_pow2 k.to.exp (k.to.refl (as_seq h0 acc)) (v b))


inline_for_extraction noextract
let lexp_fw_st (a_t:inttype_a) (len:size_t{v len > 0}) (ctx_len:size_t) (k:lexp a_t len ctx_len) =
    ctx:lbuffer (uint_t a_t SEC) ctx_len
  -> a:lbuffer (uint_t a_t SEC) len
  -> bLen:size_t
  -> bBits:size_t{0 < v bBits /\ (v bBits - 1) / bits a_t < v bLen}
  -> b:lbuffer (uint_t a_t SEC) bLen
  -> acc:lbuffer (uint_t a_t SEC) len
  -> l:size_t{0 < v l /\ v l < bits a_t /\ pow2 (v l) * v len <= max_size_t /\ v l < 32} ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h acc /\ live h ctx /\
    disjoint a b /\ disjoint a acc /\ disjoint a ctx /\
    disjoint b acc /\ disjoint b ctx /\ disjoint acc ctx /\
    BD.bn_v h b < pow2 (v bBits) /\
    k.to.linv_ctx (as_seq h ctx) /\
    k.to.linv (as_seq h a) /\ k.to.linv (as_seq h acc) /\
    k.to.refl (as_seq h acc) == k.to.exp.S.one)
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    k.to.linv (as_seq h1 acc) /\
    k.to.refl (as_seq h1 acc) ==
    S.exp_fw #k.to.a_spec k.to.exp (k.to.refl (as_seq h0 a)) (v bBits) (BD.bn_v h0 b) (v l))


inline_for_extraction noextract
val lexp_fw_raw:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:lexp a_t len ctx_len ->
  lexp_fw_st a_t len ctx_len k


inline_for_extraction noextract
val lexp_fw_ct:
    #a_t:inttype_a
  -> len:size_t{v len > 0}
  -> ctx_len:size_t
  -> k:lexp a_t len ctx_len ->
  lexp_fw_st a_t len ctx_len k
