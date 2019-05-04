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
