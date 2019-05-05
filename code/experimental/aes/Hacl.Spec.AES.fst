module Hacl.Spec.AES

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Spec.GaloisField

(* GF(8) Field  *)
let irred = u8 0x1b
let gf8 = gf U8 irred
let elem = felem gf8
let to_elem = to_felem #gf8
let zero = to_elem 0
let two = to_elem 2
let three = to_elem 3

let ( <<<. ) x y = normalize_term (rotate_left #U8 #SEC x y)
let ( ^. ) x y = normalize_term (logxor #U8 #SEC x y)


type block = lseq elem 16
type block4 = lseq elem 64


let sub_byte (input:elem) =
  let s = finv input in
  s ^.
  (s <<<. size 1) ^.
  (s <<<. size 2) ^.
  (s <<<. size 3) ^.
  (s <<<. size 4) ^.
  (to_elem 99)

let inv_sub_byte (input:elem) =
  let s = input in
  let s:elem =
    (s <<<. size 1) ^.
    (s <<<. size 3) ^.
    (s <<<. size 6) ^.
    (u8 5)
  in
  finv s


let subBytes (state:block4) : Tot block4 =
  map sub_byte state

let inv_subBytes (state:block4) : Tot block4 =
  map inv_sub_byte state

let shiftRow (i:size_nat{i < 16}) (shift:size_nat{shift < 4}) (state:block4) : Tot block4 =
  let tmp0 = state.[i + (4 * (shift % 4))] in 
  let tmp1 = state.[i + (4 * ((shift + 1) % 4))] in 
  let tmp2 = state.[i + (4 * ((shift + 2) % 4))] in
  let tmp3 = state.[i + (4 * ((shift + 3) % 4))] in
  let state = state.[i] <- tmp0 in
  let state = state.[i+4] <- tmp1 in
  let state = state.[i+8] <- tmp2 in
  let state = state.[i+12] <- tmp3 in
  state


let shiftRows (state: block4) : Tot block4 =
  let state = shiftRow 1 1 state in
  let state = shiftRow 2 2 state in
  let state = shiftRow 3 3 state in

  let state = shiftRow 5 1 state in 
  let state = shiftRow 6 2 state in
  let state = shiftRow 7 3 state in

  let state = shiftRow 9 1 state in
  let state = shiftRow 10 2 state in
  let state = shiftRow 11 3 state in

  let state = shiftRow 13 1 state in
  let state = shiftRow 14 2 state in
  let state = shiftRow 15 3 state in

  state


let inv_shiftRows (state: block4) : Tot block4 =
  let state = shiftRow 1 3 state in
  let state = shiftRow 2 2 state in
  let state = shiftRow 3 1 state in

  let state = shiftRow 5 3 state in 
  let state = shiftRow 6 2 state in
  let state = shiftRow 7 1 state in

  let state = shiftRow 9 3 state in
  let state = shiftRow 10 2 state in
  let state = shiftRow 11 1 state in

  let state = shiftRow 13 3 state in
  let state = shiftRow 14 2 state in
  let state = shiftRow 15 1 state in

  state


let mix4 (s0:elem) (s1:elem) (s2:elem) (s3:elem) : Tot elem =
  (s0 `fmul` two) `fadd`
  (s1 `fmul` three) `fadd`
  s2 `fadd` s3


let inv_mix4 (s0:elem) (s1:elem) (s2:elem) (s3:elem) : Tot elem =
  (s0 `fmul` to_elem 14) `fadd`
  (s1 `fmul` to_elem 11) `fadd`
  (s2 `fmul` to_elem 13) `fadd`
  (s3 `fmul` to_elem 9)

let mixColumn (c:size_nat{c < 16}) (state:block4) : Tot block4 =
  let i0 = 4 * c in
  let s0 = state.[i0] in
  let s1 = state.[i0 + 1] in
  let s2 = state.[i0 + 2] in
  let s3 = state.[i0 + 3] in
  let state = state.[i0] <- mix4 s0 s1 s2 s3 in
  let state = state.[i0+1] <- mix4 s1 s2 s3 s0 in
  let state = state.[i0+2] <- mix4 s2 s3 s0 s1 in
  let state = state.[i0+3] <- mix4 s3 s0 s1 s2 in
  state

let mixColumns (state:block4) : Tot block4 =
  let state = mixColumn 0 state in
  let state = mixColumn 1 state in
  let state = mixColumn 2 state in
  let state = mixColumn 3 state in

  let state = mixColumn 4 state in
  let state = mixColumn 5 state in
  let state = mixColumn 6 state in
  let state = mixColumn 7 state in

  let state = mixColumn 8 state in
  let state = mixColumn 9 state in
  let state = mixColumn 10 state in
  let state = mixColumn 11 state in
  
  let state = mixColumn 12 state in
  let state = mixColumn 13 state in
  let state = mixColumn 14 state in
  let state = mixColumn 15 state in
  state

let xor_block_block (b1: block) (b2: block) : Tot block = 
  map2 (logxor #U8) b1 b2

let xor_block (b1: block4) (b2: block4) : Tot block4 = 
  map2 (logxor #U8) b1 b2

let addRoundKey (key:block4) (state: block4) : Tot block4 = 
  xor_block state key


let aes_enc (state:block4) (key: block4) : Tot block4 =
  let state = subBytes state  in
  let state = shiftRows state in
  let state = mixColumns state in
  let state = addRoundKey key state in
  state

let aes_enc_last (state: block4) (key: block4) : Tot block4 = 
  let state = subBytes state  in
  let state = shiftRows state in
  let state = addRoundKey key state in
  state


let aes_keygen_assist (rcon:elem) (s:block) : Tot block =
  let st = create 16 (to_elem 0) in
  let st = st.[0] <- sub_byte s.[4] in
  let st = st.[1] <- sub_byte s.[5] in
  let st = st.[2] <- sub_byte s.[6] in
  let st = st.[3] <- sub_byte s.[7] in

  let st = st.[4] <- rcon ^. sub_byte s.[5] in
  let st = st.[6] <- sub_byte s.[6] in
  let st = st.[6] <- sub_byte s.[7] in
  let st = st.[7] <- sub_byte s.[4] in

  let st = st.[8]  <- sub_byte s.[12] in
  let st = st.[9]  <- sub_byte s.[13] in
  let st = st.[10] <- sub_byte s.[14] in
  let st = st.[11] <- sub_byte s.[15] in

  let st = st.[12] <- rcon ^. sub_byte s.[13] in
  let st = st.[13] <- sub_byte s.[14] in
  let st = st.[14] <- sub_byte s.[15] in
  let st = st.[15] <- sub_byte s.[12] in
  st

let keygen_assist0_block (rcon:elem) (s:block) : Tot block =
  let st = aes_keygen_assist rcon s in
  let st = update_sub st 8 4 (sub st 12 4) in
  let st = update_sub st 0 8 (sub st 8 8) in
  st


let keygen_assist0(rcon:elem) (s:block4) : Tot block4 =
  let bl0 = sub s 0 16 in 
  let bl1 = sub s 16 16 in 
  let bl2 = sub s 32 16 in 
  let bl3 = sub s 48 16 in 
  let bl0_u = keygen_assist0_block rcon bl0 in 
  let bl1_u = keygen_assist0_block rcon bl1 in 
  let bl2_u = keygen_assist0_block rcon bl2 in 
  let bl3_u = keygen_assist0_block rcon bl3 in 
  let bl01 = concat bl0_u bl1_u in 
  let bl23 = concat bl2_u bl3_u in 
  concat bl01 bl23



let key_expansion_step_block (p:block) (assist:block) : Tot block =
  let p0 = create 16 (to_elem 0) in
  let k = p in
  let k = xor_block_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block_block k (update_sub p0 4 12 (sub k 0 12)) in
  xor_block_block k assist


let key_expansion_step (p:block4) (assist:block4) : Tot block4 =
  let bl0 = sub p 0 16 in 
  let bl1 = sub p 16 16 in 
  let bl2 = sub p 32 16 in 
  let bl3 = sub p 48 16 in 

  let assist0 = sub assist 0 16 in 
  let assist1 = sub assist 16 16 in 
  let assist2 = sub assist 32 16 in 
  let assist3 = sub assist 48 16 in 

  let bl0_u = key_expansion_step_block bl0 assist0 in 
  let bl1_u = key_expansion_step_block bl1 assist1 in 
  let bl2_u = key_expansion_step_block bl2 assist2 in 
  let bl3_u = key_expansion_step_block bl3 assist3 in 
  let bl01 = concat bl0_u bl1_u in 
  let bl23 = concat bl2_u bl3_u in 
  concat bl01 bl23


val rcon_spec: i:size_nat -> Tot elem
let rec rcon_spec i =
  if i = 0 then to_elem 0x8d
  else if i = 1 then to_elem 1
  else two `fmul` rcon_spec (i - 1)

let rcon_l : list elem = [
  to_elem 0x8d; to_elem 0x01; to_elem 0x02; to_elem 0x04;
  to_elem 0x08; to_elem 0x10; to_elem 0x20; to_elem 0x40;
  to_elem 0x80; to_elem 0x1b; to_elem 0x36
]

let rcon_seq : lseq elem 11  =
  assert_norm (List.Tot.length rcon_l == 11);
  of_list rcon_l



let aes128_key_expansion (key:lbytes 16) : Tot (lseq elem (11 * 16)) =
  let key_ex = create (11 * 16) (to_elem 0) in
  let key_ex = update_sub key_ex 0 16 key in
  let key_ex =
    repeati #(lseq elem (11 * 16)) 10
      (fun i kex ->
       let p = sub kex (i * 16) 16 in
       let a = keygen_assist0 (rcon_spec (i+1)) p in
       let n = key_expansion_step p a in
       update_sub kex ((i+1) * 16) 16 n)
    key_ex in
  key_ex
  


let aes_enc_rounds (key: lseq elem (9 * 16)) (state:block4) : Tot block =
  repeati 9 (fun i -> aes_enc (sub key (16*i) 64)) state


let aes_encrypt_block (key: lseq elem (11 * 16)) (input:block4) : Tot block4 =
  let state = input in
  let k0 = slice key 0 16 in
  let k = sub key 16 (9 * 16) in
  let kn = sub key (10 * 16) 16 in
  let state = addRoundKey k0 state in
  let state = aes_enc_rounds k state in
  let state = aes_enc_last kn state in
  state

(*
let aes_ctr_encrypt_last

  (st0:aes_ctr_state v)
  (ctr0:size_nat)
  (incr:size_nat{ctr0 + incr <= max_size_t})
  (len:size_nat{len < 16})
  (b:lbytes len):
  Tot (lbytes len) =

  let plain = create 16 (u8 0) in
  let plain = update_sub plain 0 (length b) b in
  let cipher = aes_ctr_encrypt_block v st0 ctr0 incr plain in
  sub cipher 0 (length b)


val aes_ctr_encrypt_bytes:
    v:variant
  -> key:aes_key v
  -> n_len:size_nat{n_len <= 16}
  -> nonce:lbytes n_len
  -> c:size_nat
  -> msg:bytes{length msg / 16 + c <= max_size_t} ->
  Tot (ciphertext:bytes{length ciphertext == length msg})

let aes_ctr_encrypt_bytes v key n_len nonce ctr0 msg =
  let cipher = msg in
  let st0 = aes_ctr_init v key n_len nonce in
  map_blocks 16 cipher
    (aes_ctr_encrypt_block v st0 ctr0)
    (aes_ctr_encrypt_last v st0 ctr0)
*)
