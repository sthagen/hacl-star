module Hacl.Impl.AES_128.CoreBitSlice

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Hacl.Spec.AES_128.BitSlice

module ST = FStar.HyperStack.ST




type state = lbuffer uint64 8ul
type key1 =  lbuffer uint64 8ul
type nonce =  lbuffer uint64 8ul

type block = lbuffer uint8 16ul
type block4 = lbuffer uint8 64ul


inline_for_extraction
val create_state: unit ->
  StackInline state
  (requires (fun h -> True))
  (ensures (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create 8 (u64 0))))

let create_state() = create 8ul (u64 0)


inline_for_extraction
val copy_state:
    next: state
  -> prev: state ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next /\ disjoint next prev))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1))

let copy_state next prev = copy next prev


val load_block0:
    out: state
  -> inp: block ->
  ST unit
  (requires (fun h -> live h out /\ live h inp))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_block0 (out:state) (inp:block) =
  let b1 = sub inp (size 0) (size 8) in
  let b2 = sub inp (size 8) (size 8) in
  let fst = uint_from_bytes_le #U64 b1 in
  let snd = uint_from_bytes_le #U64 b2 in
  let fst = transpose_bits64 fst in
  let snd = transpose_bits64 snd in
  let h0 = ST.get() in
  Lib.Buffer.loop_nospec #h0 (size 8) out
    (fun i ->
      let sh = i *. (size 8) in
      let u = (fst >>. sh) &. u64 0xff in
      let u = u ^. (((snd >>. sh) &. u64 0xff) <<. size 8) in
      out.(i) <- u)


val transpose_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\ (
    seqToTuple (as_seq h1 st) == transpose_bits64x8 (seqToTuple (as_seq h0 st))
  )))

let transpose_state st =
  let i0 = st.(size 0) in
  let i1 = st.(size 1) in
  let i2 = st.(size 2) in
  let i3 = st.(size 3) in
  let i4 = st.(size 4) in
  let i5 = st.(size 5) in
  let i6 = st.(size 6) in
  let i7 = st.(size 7) in
  let (t0,t1,t2,t3,t4,t5,t6,t7) =
    transpose_bits64x8 (i0, i1, i2, i3, i4, i5, i6, i7) in
  st.(size 0) <- t0;
  st.(size 1) <- t1;
  st.(size 2) <- t2;
  st.(size 3) <- t3;
  st.(size 4) <- t4;
  st.(size 5) <- t5;
  st.(size 6) <- t6;
  st.(size 7) <- t7


val store_block0:
    out: block
  -> inp: state ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let store_block0 out (inp:state) =
  let (t0,t1,t2,t3,t4,t5,t6,t7) =
    transpose_bits64x8 (inp.(size 0), inp.(size 1), inp.(size 2), inp.(size 3), inp.(size 4), inp.(size 5), inp.(size 6), inp.(size 7))
  in
  uint_to_bytes_le #U64 (sub out (size 0) (size 8)) t0;
  uint_to_bytes_le #U64 (sub out (size 8) (size 8)) t1


val load_key1:
    out: key1
  -> k: block ->
  Stack unit
  (requires (fun h -> live h out /\ live h k))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_key1 (out:state) (k:block) =
  load_block0 out k;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out
    (fun i ->
      let u = out.(i) in
      let u = u ^. (u <<. size 16) in
      let u = u ^. (u <<. size 32) in
      out.(i) <- u)


val load_nonce:
    out: nonce
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h out /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_nonce out nonce =
  push_frame();
  let nb = create 16ul (u8 0) in
  copy (sub nb 0ul 12ul) nonce;
  load_key1 out nb;
  pop_frame()


#set-options "--z3rlimit 100"

val load_state:
    out: state
  -> nonce: nonce
  -> counter: size_t ->
  Stack unit
  (requires (fun h -> live h out /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_state out nonce counter =
  push_frame();
  let ctr = create 16ul (u8 0) in
  uint_to_bytes_be #U32  (sub ctr (size 0) (size 4)) (secret counter);
  uint_to_bytes_be #U32  (sub ctr (size 4) (size 4)) (secret (counter +. 1ul));
  uint_to_bytes_be #U32  (sub ctr (size 8) (size 4)) (secret (counter +. 2ul));
  uint_to_bytes_be #U32  (sub ctr (size 12) (size 4)) (secret (counter +. 3ul));
  load_block0 out ctr;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out
    (fun i ->
      let u = out.(i) in
      let u = (u <<. size 12) |. (u <<. size 24) |. (u <<. size 36) |. (u <<. size 48) in
      let u = u &. u64 0xf000f000f000f000 in
      out.(i) <- u ^. nonce.(i));
  pop_frame ()


val xor_state_key1:
    st: state
  -> ost: state ->
  Stack unit
  (requires (fun h -> live h st /\ live h ost))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\ seqToTuple (as_seq h1 st) == xor_state_s (seqToTuple (as_seq h0 st)) (seqToTuple (as_seq h0 ost))))

let xor_state_key1 st ost =
  let (st0, st1, st2, st3, st4, st5, st6, st7) = 
    xor_state_s 
      (st.(size 0), st.(size 1), st.(size 2), st.(size 3),st.(size 4), st.(size 5), st.(size 6), st.(size 7))
      (ost.(size 0), ost.(size 1), ost.(size 2), ost.(size 3), ost.(size 4), ost.(size 5), ost.(size 6), ost.(size 7)) in 
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7


val xor_block:
    out: lbuffer uint8 64ul
  -> st: state
  -> b: lbuffer uint8 64ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h out /\ live h b))
  (ensures (fun h0 _ h1 -> modifies2 out st h0 h1))

let xor_block out st inp =
  transpose_state st;
  let h1 = ST.get () in
  loop_nospec #h1 (size 8) out
    (fun j ->
      let ob = sub out (j *. size 8) (size 8) in
      let ib = sub inp (j *. size 8) (size 8) in
      let u = uint_from_bytes_le #U64 ib in
      uint_to_bytes_le #U64 ob (u ^. st.(j)))


val sub_bytes_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\ seqToTuple (as_seq h1 st) == sub_bytes64x8 (seqToTuple (as_seq h0 st))
    /\ as_seq h1 st == sub_bytes_state_as_seq (as_seq h0 st)
))

let sub_bytes_state (st:state) =
  let (st0,st1,st2,st3,st4,st5,st6,st7) =
    sub_bytes64x8 (st.(size 0), st.(size 1), st.(size 2), st.(size 3),st.(size 4), st.(size 5), st.(size 6), st.(size 7))
  in
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7


val shift_rows_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\ seqToTuple (as_seq h1 st) == shift_row_state_s (seqToTuple (as_seq h0 st)) /\
  as_seq h1 st == shift_row_state_as_seq (as_seq h0 st)))

let shift_rows_state st =
  let (st0,st1,st2,st3,st4,st5,st6,st7) = shift_row_state_s  (st.(size 0), st.(size 1), st.(size 2), st.(size 3),st.(size 4), st.(size 5), st.(size 6), st.(size 7)) in 
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7
 
 

val mix_columns_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\ seqToTuple (as_seq h1 st) == mix_col64x8 (seqToTuple (as_seq h0 st))))

let mix_columns_state st =
let (st0, st1, st2, st3, st4, st5, st6, st7) = mix_col64x8 (st.(size 0), st.(size 1), st.(size 2), st.(size 3),
						st.(size 4), st.(size 5), st.(size 6), st.(size 7))
  in
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7

#reset-options "--z3rlimit  100"

val aes_enc:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\ as_seq h1 st == aes_enc_s (as_seq h0 st) (as_seq h0 key)))

let aes_enc st key =
    let h0 = ST.get() in 
  sub_bytes_state st;
  shift_rows_state st;
  mix_columns_state st;
  xor_state_key1 st key;
    let h1 = ST.get() in 
  assert(Seq.equal (as_seq h1 st) (aes_enc_s (as_seq h0 st) (as_seq h0 key)))

val aes_enc_last:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let aes_enc_last st key =
  sub_bytes_state st;
  shift_rows_state st;
  xor_state_key1 st key


let rcon : b:ilbuffer uint8 11ul =
  [@ inline_let]
  let rcon_l = [
    u8(0x8d); u8(0x01); u8(0x02); u8(0x04);
    u8(0x08); u8(0x10); u8(0x20); u8(0x40);
    u8(0x80); u8(0x1b); u8(0x36)
  ] in
  assert_norm (List.Tot.length rcon_l == 11);
  createL_global rcon_l


inline_for_extraction
val aes_keygen_assisti: rcon:uint8 -> i:shiftval U8 -> u:uint64 -> Tot uint64
let aes_keygen_assisti rcon i u =
  (* 
  let n = (u &. u64 0xf000f000f000f000) >>. size 12 in
  let n = ((n >>. size 1) |. (n <<. size 3)) &. u64  0x000f000f000f000f in
  let ri = to_u64 ((rcon >>. i) &. u8 1) in
  let ri = ri ^. (ri <<. size 16) in
  let ri = ri ^. (ri <<. size 32) in
  let n = n ^. ri in
  let n = n <<. size 12 in
  n *)
  aes_key_assisti_s rcon i u


val aes_keygen_assist:
    next: state
  -> prev: state
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h next /\ live h prev /\ disjoint next prev))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1 /\ seqToTuple (as_seq h1 next) == aes_key_assist_s (seqToTuple (as_seq h0 prev)) rcon))

let aes_keygen_assist next prev rcon =
  let (next0, next1, next2, next3, next4, next5, next6, next7)  =  aes_key_assist_s (prev.(size 0), prev.(size 1), prev.(size 2), prev.(size 3), prev.(size 4), prev.(size 5), prev.(size 6), prev.(size 7)) rcon in 
  next.(size 0) <- next0;
  next.(size 1) <- next1;
  next.(size 2) <- next2;
  next.(size 3) <- next3;
  next.(size 4) <- next4;
  next.(size 5) <- next5;
  next.(size 6) <- next6;
  next.(size 7) <- next7


inline_for_extraction
let key_expand1 (p:uint64) (n:uint64) = key_expand1_s p n

val key_expansion_step:
    next: state
  -> prev: state ->
  ST unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1 /\ seqToTuple (as_seq h1 next) == key_expansion_step_s (seqToTuple (as_seq h0 prev)) (seqToTuple (as_seq h0 next))
  ))


let key_expansion_step next prev =
  let (next0, next1, next2, next3, next4, next5, next6, next7) = 
    key_expansion_step_s (prev.(size 0), prev.(size 1), prev.(size 2), prev.(size 3), prev.(size 4), prev.(size 5), prev.(size 6), prev.(size 7))  
    (next.(size 0), next.(size 1), next.(size 2), next.(size 3), next.(size 4), next.(size 5), next.(size 6), next.(size 7)) in 
  next.(size 0) <- next0;
  next.(size 1) <- next1;
  next.(size 2) <- next2;
  next.(size 3) <- next3;
  next.(size 4) <- next4;
  next.(size 5) <- next5;
  next.(size 6) <- next6;
  next.(size 7) <- next7
