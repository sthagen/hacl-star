module Hacl.Impl.AES_128.Generic

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.AES_128.Core


module ST = FStar.HyperStack.ST

type variant = | AES128 | AES256

let num_rounds (v: variant) = 
  match v with 
  | AES128 -> 10 
  | AES256 -> 14 

noextract inline_for_extraction
let key_size (v: variant) = 
  match v with 
  |AES128 -> 16ul
  |AES256 -> 32ul

noextract inline_for_extraction
let nb = 4

noextract inline_for_extraction 
let nk (v: variant) = 
  match v with 
  |AES128 -> 4
  |AES256 -> 8

noextract inline_for_extraction 
let nr (v: variant) = 
  match v with 
  |AES128 -> 10ul 
  |AES256 -> 14ul

noextract inline_for_extraction 
let keyex_size (v: variant) = 
  match v with 
  |AES128 -> 11ul
  |AES256 -> 15ul

noextract inline_for_extraction 
let keyr_size (v: variant) = 
  match v with 
  |AES128 -> 9ul
  |AES256 -> 13ul

noextract inline_for_extraction 
let skey_lenght (v: variant) = 
  match v with 
  |AES128 -> 16ul
  |AES256 -> 32ul


#set-options "--z3rlimit 100"


(* ??? *)
unfold let ctxlen (m:m_spec) (v: variant) =  nlen m +. (keyex_size v *. klen m)
 

unfold type keyr (m: m_spec) (v: variant) = lbuffer (stelem m) (keyr_size v *. klen m)
unfold type keyex (m: m_spec) (v: variant) = lbuffer (stelem m) (keyex_size v *. klen m)
unfold type skey (m: m_spec) (v: variant) = lbuffer uint8 (key_size v)

unfold type nonce_t = lbuffer uint8 12ul

unfold type aes_ctx (m:m_spec) (v: variant) = lbuffer (stelem m) (ctxlen m v)


inline_for_extraction
val get_nonce: 
    #m: m_spec
  -> #v: variant   
  -> ctx: aes_ctx m v ->
  Stack (lbuffer (stelem m) (nlen m))
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx 0ul (nlen m)))

inline_for_extraction
let get_nonce #m #v ctx = sub ctx (size 0) (nlen m)


inline_for_extraction
val get_kex:
    #m: m_spec  
  -> #v: variant  
  -> ctx: aes_ctx m v ->
  Stack (keyex m v)
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx (nlen m ) ((keyex_size v) *. klen m)))

inline_for_extraction
let get_kex #m #v ctx = sub ctx (nlen m) ((keyex_size v) *. klen m)


inline_for_extraction
val create_ctx: m: m_spec ->
  v: variant ->
  StackInline (aes_ctx m v)
  (requires (fun h -> True))
  (ensures (fun h0 f h1 -> live h1 f))

let create_ctx m v = create (ctxlen m v) (elem_zero m)


inline_for_extraction
val add_round_key:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let add_round_key #m st key = xor_state_key1 #m st key

inline_for_extraction
val enc_rounds: 
    #m: m_spec
  -> #var: variant   
  -> st: state m
  -> key: keyr m var 
  -> n: size_t{v n <= uint_v (nr var) - 1 } ->
  ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let enc_rounds #m #v st key n =
  let h0 = ST.get() in
  loop_nospec #h0 n st
    (fun i -> let sub_key = sub key (i *. klen m) (klen m) in
    (* I have not yet changed the lenght of the key for aes_encrypt*)
    admit();
    aes_enc #m st sub_key)
 
#reset-options "--z3refresh --z3rlimit  100"

inline_for_extraction
val block_cipher:
    #m: m_spec
  -> #var: variant  
  -> st: state m
  -> key: keyex m var ->
  ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let block_cipher #m #var st key =
  let n = nr var in 
  let inner_rounds = n -. size 1 in
  let klen = klen m in
  let k0 = sub key (size 0) klen in
  let kr = sub key klen (inner_rounds *. klen) in
  let kn = sub key (n *. klen) klen in
  add_round_key #m st k0;
  enc_rounds #m #var st kr (n -. size 1);
  aes_enc_last #m st kn
  

#set-options "--admit_smt_queries true"


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
val key_expansion128:
    #m: m_spec
  -> keyx: keyex m AES128 
  -> key:skey m AES128 ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc keyx) h0 h1))

[@ CInline ]
let key_expansion128 #m keyx key =
  let klen = klen m in
  load_key1 (sub keyx (size 0) klen) key;
  let h0 = ST.get() in
  [@inline_let]
  let spec h = Hacl.Spec.AES_128.BitSlice.key_expansion128_inner in 
  loop1 h0 (size 10) keyx spec
    (fun i ->
     let prev = sub keyx (klen *. i) klen in
     let next = sub keyx (klen *. (i +. size 1)) klen in
     let rcon_ = index rcon (i +. size 1) in 
     aes_keygen_assist next prev rcon_;
     key_expansion_step #m next prev)


inline_for_extraction
val key_expansion256:
    #m: m_spec
  -> keyx: keyex m AES256
  -> key: skey m AES256 ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc keyx) h0 h1))

let key_expansion256 #m keyx key =
  let klen = klen m in
  load_key1 (sub keyx (size 0) klen) (sub key (size 0) (size 16));
  load_key1 (sub keyx klen klen) (sub key (size 16) (size 16));
  let h0 = ST.get() in
  (* I WOULD LIKE TO HAVE A LOOP HERE BUT AES_KEYGEN_ASSIST #M INSISTS ON AN IMMEDIATE RCON *)
  (* MAYBE WE SHOULD UNROLL ONLY THIS LOOP *)
  let prev0 = sub keyx (size 0) (klen) in
  let prev1 = sub keyx (klen) (klen) in
  let next0 = sub keyx (klen *. size 2) (klen) in
  let next1 = sub keyx (klen *. size 3) (klen) in
  aes_keygen_assist #m next0 prev1 (u8 0x01);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist #m next1 next0 (u8 0x00);
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 4) (klen) in
  let next1 = sub keyx (klen *. size 5) (klen) in
  aes_keygen_assist #m next0 prev1 (u8 0x02);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist #m next1 next0 (u8 0x00);
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 6) (klen) in
  let next1 = sub keyx (klen *. size 7) (klen) in
  aes_keygen_assist #m next0 prev1 (u8 0x04);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist #m next1 next0 (u8 0x00);
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 8) (klen) in
  let next1 = sub keyx (klen *. size 9) (klen) in
  aes_keygen_assist #m next0 prev1 (u8 0x08);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist #m next1 next0 (u8 0x00);
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 10) (klen) in
  let next1 = sub keyx (klen *. size 11) (klen) in
  aes_keygen_assist #m next0 prev1 (u8 0x10);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist #m next1 next0 (u8 0x00);
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 12) (klen) in
  let next1 = sub keyx (klen *. size 13) (klen) in
  aes_keygen_assist #m next0 prev1 (u8 0x20);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist #m next1 next0 (u8 0x00);
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 14) (klen) in
  aes_keygen_assist #m next0 prev1 (u8 0x40);
  key_expansion_step #m next0 prev0
(* END PATTERN *)


inline_for_extraction
val key_expansion:
    #m: m_spec
  -> #v: variant   
  -> keyx: keyex m v
  -> key: skey m v ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc keyx) h0 h1))

let key_expansion #m #v keyx key = 
  match v with 
  |AES128 -> key_expansion128 keyx key
  |AES256 -> key_expansion256 keyx key

#set-options "--admit_smt_queries false"


inline_for_extraction
val aes_init_:
    #m: m_spec  
  -> #v: variant   
  -> ctx: aes_ctx m v
  -> key: skey m v 
  -> nonce: nonce_t ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 20"

let aes_init_ #m #v ctx key nonce =
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  key_expansion kex key;
  load_nonce  n nonce


(* PATTERN FOR AVOIDING INLINING *)
val aes128_init_bitslice:
  ctx: aes_ctx  M32 AES128
  -> key: skey M32 AES128 
  -> nonce: nonce_t ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes128_init_bitslice ctx key nonce = aes_init_ #M32 #AES128 ctx key nonce


[@ CInline]
inline_for_extraction
val aes128_init_ni:
    ctx: aes_ctx MAES AES128
  -> key: skey MAES AES128
  -> nonce: nonce_t ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes128_init_ni ctx key nonce = aes_init_ #MAES #AES128 ctx key nonce

(* change?  *)
inline_for_extraction
val aes128_init:
    #m :m_spec
  -> ctx: aes_ctx m AES128
  -> key: skey m AES128
  -> nonce: nonce_t ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes128_init #m  ctx key nonce =
    match m with
    | M32 -> aes128_init_bitslice ctx key nonce
    | MAES -> aes128_init_ni ctx key nonce
    



inline_for_extraction
val aes_init:
    #m :m_spec
  -> #v: variant 
  -> ctx: aes_ctx m v
  -> key: skey m v
  -> nonce: nonce_t ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes_init #m #v ctx key nonce =
  match v with 
  |AES256 -> aes_init_ ctx key nonce
  |AES128 -> aes128_init ctx key nonce
    


(*inline_for_extraction
val aes128_set_nonce:
    #m: m_spec
  -> ctx: aes_ctx m AES128
  -> nonce: nonce_t ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes128_set_nonce #m ctx nonce =
  let n = get_nonce ctx in
  load_nonce #m n nonce
*)

inline_for_extraction
val aes_set_nonce: 
  #m: m_spec 
  -> #v: variant 
  -> ctx: aes_ctx m v 
  -> nonce: nonce_t ->
  ST unit 
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes_set_nonce #m #v ctx nonce = 
  let n = get_nonce ctx in 
  load_nonce #m n nonce


(*
inline_for_extraction
val aes128_encrypt_block:
    #m: m_spec
  -> ob: lbuffer uint8 16ul
  -> ctx: aes_ctx m AES128
  -> ib: lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h ob /\ live h ctx /\ live h ib))
  (ensures (fun h0 _ h1 -> modifies (loc ob) h0 h1))

let aes128_encrypt_block #m ob ctx ib =
  push_frame();
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  let st = create_state #m in
  load_block0 st ib;
  block_cipher st kex;
  store_block0 ob st;
  pop_frame()
*)

inline_for_extraction
val aes_encrypt_block:
    #m: m_spec
  -> #v: variant   
  -> ob: lbuffer uint8 16ul
  -> ctx: aes_ctx m v
  -> ib: lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h ob /\ live h ctx /\ live h ib))
  (ensures (fun h0 _ h1 -> modifies (loc ob) h0 h1))

let aes_encrypt_block #m #v ob ctx ib =
  push_frame();
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  let st = create_state #m in
  load_block0 st ib;
  block_cipher st kex;
  store_block0 ob st;
  pop_frame()

(*
inline_for_extraction
val aes128_key_block:
    #m: m_spec
  -> kb: lbuffer uint8 16ul
  -> ctx: aes_ctx m AES128
  -> counter: size_t ->
  ST unit
  (requires (fun h -> live h kb /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc kb) h0 h1))

let aes128_key_block #m kb ctx counter =
  push_frame();
  let kex = get_kex  ctx in
  let n = get_nonce ctx in
  let st = create_state #m in
  load_state #m st n counter;
  block_cipher  st kex;
  store_block0  kb st;
  pop_frame()
*)

inline_for_extraction
val aes_key_block:
    #m: m_spec
  -> #v: variant   
  -> kb: lbuffer uint8 16ul
  -> ctx: aes_ctx m v
  -> counter: size_t ->
  ST unit
  (requires (fun h -> live h kb /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc kb) h0 h1))

let aes_key_block #m #v kb ctx counter =
  push_frame();
  let kex = get_kex  ctx in
  let n = get_nonce ctx in
  let st = create_state #m in
  load_state #m st n counter;
  block_cipher  st kex;
  store_block0  kb st;
  pop_frame()



inline_for_extraction
val aes_update4:
    #m: m_spec
  -> #var: variant   
  -> out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx m var 
  -> counter: size_t ->
  ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 b h1 -> modifies (loc out) h0 h1))

let aes_update4 #m #var out inp ctx ctr =
  push_frame();
  let st = create_state #m in
  let kex = get_kex #m ctx in
  let n = get_nonce #m ctx in
  load_state st n ctr;
  block_cipher st kex;
  xor_block  out st inp;
  pop_frame()


inline_for_extraction
val aes_ctr_:
    #m: m_spec
  -> #v: variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx m v
  -> counter: size_t ->
  ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes_ctr_ #m #v len out inp ctx counter  =
  push_frame();
  let rounds = nr v in 
  let blocks64 = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec #h0 blocks64 out
    (fun i ->
      let ctr = counter +. (i *. size 4) in
      let ib = sub inp (i *. size 64) (size 64) in
      let ob = sub out (i *. size 64) (size 64) in
      aes_update4 #m ob ib ctx ctr);
  let rem = len %. size 64 in
  if (rem >. size 0) then (
    let ctr = counter +. (blocks64 *. size 4) in
    let ib = sub inp (blocks64 *. size 64) rem in
    let ob = sub out (blocks64 *. size 64) rem in
    let last = create 64ul (u8 0) in
    copy (sub last 0ul rem) ib;
    aes_update4 #m last last ctx ctr ;
    copy ob (sub last 0ul rem));
  pop_frame()


(* PATTERN FOR AVOIDING INLINING *)
val aes_ctr_bitslice:
  #v: variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx M32 v
  -> counter: size_t ->
  
  ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes_ctr_bitslice #v len out inp ctx counter  = aes_ctr_ #M32 len out inp ctx counter 


inline_for_extraction
val aes_ctr_ni:
  #v: variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx MAES v
  -> counter: size_t -> 
  ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes_ctr_ni #v len out inp ctx counter = aes_ctr_ #MAES len out inp ctx counter

#reset-options "--z3refresh"
inline_for_extraction 
val aes_ctr:
    #m: m_spec
  -> #v: variant  
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx m v
  -> counter: size_t ->
  ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))


let aes_ctr #m #v len out inp ctx counter  =
  match m with
  | M32 -> aes_ctr_bitslice #v len out inp ctx counter
  | MAES -> aes_ctr_ni #v len out inp ctx counter
(* END PATTERN *)


inline_for_extraction
let aes_ctr_encrypt (#m: m_spec) (#v: variant) in_len out inp k n c = 
  push_frame();
  let ctx = create_ctx m v in  
  aes_init #m #v ctx k n;
  aes_ctr #m #v in_len out inp ctx c;
  pop_frame()

inline_for_extraction 
let aes_ctr_decrypt  (#m: m_spec) (#v: variant) in_len out inp k n c = 
  aes_ctr_encrypt #m #v in_len out inp k n c

inline_for_extraction
let aes128_ctr_encrypt (#m: m_spec) in_len out inp k n c = 
  aes_ctr_encrypt #m #AES128 in_len out inp k n c

inline_for_extraction
let aes128_ctr_decrypt (#m: m_spec) in_len out inp k n c = 
  aes128_ctr_encrypt #m in_len out inp n k c


inline_for_extraction
let aes256_ctr_encrypt (#m: m_spec) in_len out inp k n c = 
  aes_ctr_encrypt #m #AES256 in_len out inp k n c

inline_for_extraction
let aes256_ctr_decrypt (#m: m_spec) in_len out inp k n c = 
  aes256_ctr_encrypt #m in_len out inp k n c
