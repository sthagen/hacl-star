module Hacl.Impl.AES_128.Core

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.Vec128

module ST = FStar.HyperStack.ST

open Hacl.Spec.AES_128.BitSlice


type m_spec =
  | MAES
  | M32

unfold
let stelem (m:m_spec) =
  match m with
  | MAES -> vec128
  | M32 -> uint64

unfold
let stlen (m:m_spec) =
  match m with
  | MAES -> 4ul
  | M32 -> 8ul

unfold
let klen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold
let nlen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold
let elem_zero (m:m_spec) : stelem m =
  match m with
  | M32 -> u64 0
  | MAES -> vec128_zero

unfold
let state (m:m_spec) = lbuffer (stelem m) (stlen m)

unfold
let key1 (m:m_spec) = lbuffer (stelem m) (klen m)

unfold
let nonce (m:m_spec) = lbuffer (stelem m) (nlen m)


inline_for_extraction
val create_state:
  #m: m_spec ->
  StackInline (state m)
  (requires (fun h -> True))
  (ensures  (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create (v (stlen m)) (elem_zero m))))


inline_for_extraction
val copy_state:
    #m: m_spec
  -> st: state m
  -> ost: state m ->
  Stack unit
  (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction
val load_block0:
    #m: m_spec
  -> st: state m
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction
val load_key1:
    #m: m_spec
  -> k: key1 m
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h k /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 k h0 h1))

inline_for_extraction
val load_nonce:
    #m: m_spec
  -> n: nonce m
  -> b: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h n /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 n h0 h1))

inline_for_extraction
val load_state:
    #m: m_spec
  -> st: state m
  -> nonce: nonce m
  -> counter: size_t ->
  Stack unit
  (requires (fun h -> live h st /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction
val store_block0:
    #m: m_spec
  -> out: lbuffer uint8 16ul
  -> st: state m ->
  Stack unit
  (requires (fun h -> live h st /\ live h out))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1))


(* the method is used uniquely inn the add_round_key in Generic, so I expect that it should be this *)
inline_for_extraction
val xor_state_key1:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (
      match m with 
      |M32 -> seqToTuple (as_seq h1 st) == xor_state_s (seqToTuple (as_seq h0 st)) (seqToTuple (as_seq h0 key)) /\
	seqToBlock4 (as_seq h1 st) == Hacl.Spec.AES.xor_block (seqToBlock4 (as_seq h0 st)) (seqToBlock4(as_seq h0 key))
      |MAES -> True
	     
  )))

inline_for_extraction
val xor_block:
    #m: m_spec
  -> out: lbuffer uint8 64ul
  -> st: state m
  -> b: lbuffer uint8 64ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h out /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies2 out st h0 h1(* /\ S.xor_block (transposeStateSeq (as_seq h0 st)) (as_seq h0 b) == (as_seq h1 out)*)
  ))

(*let aes_enc (key:block) (state:block) : Tot block *)
inline_for_extraction
val aes_enc:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (
      match m with 
      |M32 -> as_seq h1 st == aes_enc_s (as_seq h0 st) (as_seq h0 key)
      |MAES -> True
    )
))

(*  let aes_enc_last (key:block) (state:block) : Tot block *)
inline_for_extraction
val aes_enc_last:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1(* /\ (as_seq h1 st) == S.aes_enc_last (as_seq h0 st) (as_seq h0 key)*)))

(*let aes_keygen_assist (rcon:elem) (s:block) : Tot block *)
inline_for_extraction
val aes_keygen_assist:
    #m: m_spec
  -> next: key1 m
  -> prev: key1 m
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h next /\ live h prev /\ disjoint prev next))
  (ensures  (fun h0 _ h1 -> modifies1 next h0 h1 /\ (
    match m with 
    |M32 -> seqToTuple (as_seq h1 next) == aes_key_assist_s (seqToTuple (as_seq h0 prev)) rcon
    |MAES -> True)
    ))

(*let key_expansion_step (p:block) (assist:block) : Tot block *)
inline_for_extraction
val key_expansion_step:
    #m: m_spec
  -> next: key1 m
  -> prev: key1 m ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures  (fun h0 _ h1 -> modifies1 next h0 h1 /\ (
    match m with 
    |M32 -> seqToTuple (as_seq h1 next) == key_expansion_step_s (seqToTuple (as_seq h0 prev)) (seqToTuple (as_seq h0 next))
    |MAES -> True)
    ))

(*
inline_for_extraction
val key_expansion_step2:
    #m: m_spec
  -> next: key1 m
  -> prev: key1 m ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures  (fun h0 _ h1 -> modifies1 next h0 h1))
*)
