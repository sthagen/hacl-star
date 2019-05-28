module Hacl.AES_128.NI

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.AES_128.Core
open Hacl.Impl.AES_128.Generic

module ST = FStar.HyperStack.ST



let state = state MAES
let key1 = key1 MAES
let keyr = keyr MAES AES128
let keyex = keyex MAES AES128
let aes_ctx = aes_ctx MAES AES128


[@ CInline ]
val create_ctx: unit ->
  StackInline  aes_ctx
  (requires (fun h -> True))
  (ensures  (fun h0 f h1 -> live h1 f))

[@ CInline ]
let create_ctx () = create_ctx 


[@ CInline ]
val aes128_init:
    ctx: aes_ctx
  -> key: skey MAES AES128
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1))

[@ CInline ]
let aes128_init ctx key nonce = aes_init #MAES #AES128 ctx key nonce


[@ CInline ]
val aes128_set_nonce:
    ctx: aes_ctx
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1))

[@ CInline ]
let aes128_set_nonce ctx nonce = aes_set_nonce #MAES #AES128 ctx nonce


[@ CInline ]
val aes128_key_block:
    kb: lbuffer uint8 16ul
  -> ctx:aes_ctx
  -> counter:size_t ->
  Stack unit
  (requires (fun h -> live h kb /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 kb h0 h1))

[@ CInline ]
let aes128_key_block kb ctx counter = aes_key_block #MAES #AES128 kb ctx counter


inline_for_extraction
val aes128_update4:
    out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx
  -> counter: size_t ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1))

let aes128_update4 out inp ctx ctr = aes_update4 #MAES #AES128 out inp ctx ctr


[@ CInline ]
val aes128_ctr:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx
  -> counter:size_t ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1))

[@ CInline ]
let aes128_ctr len out inp ctx counter  = aes_ctr #MAES #AES128 len out inp ctx counter


[@ CInline ]
let aes128_ctr_encrypt len out inp k n c = aes_ctr_encrypt #MAES #AES128 len out inp k n c


[@ CInline ]
let aes128_ctr_decrypt len out inp k n c = aes_ctr_decrypt #MAES #AES128 len out inp k n c
