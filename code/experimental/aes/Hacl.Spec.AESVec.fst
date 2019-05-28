module Hacl.Spec.AESVec


open Lib.IntTypes 
open Lib.Sequence


type u1x16 = lseq uint1 16
type xN = f: size_nat {f == 1 \/ f == 2 \/ f == 4 \/ f == 8}
type uint16xN (n: xN) = lseq u1x16 n
type state (n: xN) = lseq (uint16xN n) 8

type state_tuple (n: xN) = uint16xN n * uint16xN n * uint16xN n * uint16xN n* uint16xN n* uint16xN n* uint16xN n* uint16xN n

open FStar.Mul 

type bytesN (n: xN) = lseq (lseq uint8 16) n


assume val transpose : #n: xN ->   s: state_tuple n -> bytesN n
assume val invTranspose: #n : xN -> bytesN n -> state_tuple n
assume val lemmaTranspose: #n: xN -> s: state_tuple n -> Lemma (invTranspose (transpose s) == s)


val logand_u1x16: u1x16 -> u1x16 -> u1x16
let logand_u1x16 a b = map2 logand a b 

val logor_u1x16: u1x16 -> u1x16 -> u1x16
let logor_u1x16 a b = map2 logor a b

val logxor_u1x16: u1x16 -> u1x16 -> u1x16
let logxor_u1x16 a b = map2 logxor a b

assume val shiftLeft_u1x16: u1x16 ->  size_t -> u1x16
assume val shiftRight_u1x16: u1x16 -> size_t -> u1x16


val x16And: #n: xN -> uint16xN n -> uint16xN n ->  uint16xN n
let x16And #n a b = map2 logand_u1x16 a b 

val x16Or: #n: xN -> uint16xN n -> uint16xN n -> uint16xN n 
let x16Or #n a b = map2 logor_u1x16 a b 

val x16Xor: #n: xN -> uint16xN n -> uint16xN n -> uint16xN n
let x16Xor #n a b = map2 logxor_u1x16 a b 

val x16Not: #n: xN -> uint16xN n -> uint16xN n
let x16Not #n a = map (fun a -> map lognot a) a

val x16ShiftLeft: #n: xN -> uint16xN n -> s: size_t -> uint16xN n
let x16ShiftLeft #n a s = 
  map (fun bl -> shiftLeft_u1x16 bl s) a

val x16ShiftRight: #n: xN -> uint16xN n -> s: size_t-> uint16xN n
let x16ShiftRight #n a s = 
  map (fun bl -> shiftRight_u1x16 bl s) a


let ( &! ) = logand_u1x16 
let ( |! ) = logor_u1x16 
let ( >>! ) = shiftRight_u1x16 
let ( <<! ) = shiftLeft_u1x16 
let ( ^! ) = logxor_u1x16


let ( &. ) #n = x16And #n
let ( |. ) #n = x16Or #n
let ( ^. ) #n = x16Xor #n
let ( ~. ) #n = x16Not #n 
let ( <<. ) #n = x16ShiftLeft #n
let ( >>. ) #n = x16ShiftRight #n


assume val _subBytes: uint8 -> uint8

val subBytes: #n: xN -> s: state_tuple n -> (r : state_tuple n {
  let transposed : lseq (lseq uint8 16) n = transpose s in 
  let app = map (fun a -> map _subBytes a) transposed in 
  let inv_transposed = invTranspose app in 
  r == inv_transposed})

let subBytes #n (st0, st1, st2, st3, st4, st5, st6, st7)  = 
  let u0 = st7 in
  let u1 = st6 in
  let u2 = st5 in
  let u3 = st4 in
  let u4 = st3 in
  let u5 = st2 in
  let u6 = st1 in
  let u7 = st0 in

  let t1 = u6 ^. u4 in
  let t2 = u3 ^. u0 in
  let t3 = u1 ^. u2 in
  let t6 = u1 ^. u5 in
  let t7 = u0 ^. u6 in
  let t13 = u2 ^. u5 in
  let t16 = u0 ^. u5 in
  let t18 = u6 ^. u5 in

  let t4 = u7 ^. t3 in
  let t5 = t1 ^. t2 in
  let t8 = t1 ^. t6 in
  let t9 = u6 ^. t4 in

  let t10 = u3 ^. t4 in
  let t11 = u7 ^. t5 in
  let t12 = t5 ^. t6 in
  let t14 = t3 ^. t5 in
  let t15 = u5 ^. t7 in
  let t17 = u7 ^. t8 in
  let t19 = t2 ^. t18 in
  let t22 = u0 ^. t4 in
  let t54 = t2 &. t8 in
  let t50 = t9 &. t4 in

  let t20 = t4 ^. t15 in
  let t21 = t1 ^. t13 in
  let t39 = t21 ^. t5 in
  let t40 = t21 ^. t7 in
  let t41 = t7 ^. t19 in
  let t42 = t16 ^. t14 in
  let t43 = t22 ^. t17 in
  let t44 = t19 &. t5 in
  let t45 = t20 &. t11 in
  let t47 = t10 &. u7 in
  let t57 = t16 &. t14 in

  let t46 = t12 ^. t44 in
  let t48 = t47 ^. t44 in
  let t49 = t7 &. t21 in
  let t51 = t40 ^. t49 in
  let t52 = t22 &. t17 in
  let t53 = t52 ^. t49 in

  let t55 = t41 &. t39 in
  let t56 = t55 ^. t54 in
  let t58 = t57 ^. t54 in
  let t59 = t46 ^. t45 in
  let t60 = t48 ^. t42 in
  let t61 = t51 ^. t50 in
  let t62 = t53 ^. t58 in
  let t63 = t59 ^. t56 in
  let t64 = t60 ^. t58 in
  let t65 = t61 ^. t56 in
  let t66 = t62 ^. t43 in
  let t67 = t65 ^. t66 in
  let t68 = t65 &. t63 in
  let t69 = t64 ^. t68 in
  let t70 = t63 ^. t64 in
  let t71 = t66 ^. t68 in
  let t72 = t71 &. t70 in
  let t73 = t69 &. t67 in
  let t74 = t63 &. t66 in
  let t75 = t70 &. t74 in
  let t76 = t70 ^. t68 in
  let t77 = t64 &. t65 in
  let t78 = t67 &. t77 in
  let t79 = t67 ^. t68 in
  let t80 = t64 ^. t72 in
  let t81 = t75 ^. t76 in
  let t82 = t66 ^. t73 in
  let t83 = t78 ^. t79 in
  let t84 = t81 ^. t83 in
  let t85 = t80 ^. t82 in
  let t86 = t80 ^. t81 in
  let t87 = t82 ^. t83 in
  let t88 = t85 ^. t84 in
  let t89 = t87 &. t5 in
  let t90 = t83 &. t11 in
  let t91 = t82 &. u7 in
  let t92 = t86 &. t21 in
  let t93 = t81 &. t4 in
  let t94 = t80 &. t17 in
  let t95 = t85 &. t8 in
  let t96 = t88 &. t39 in
  let t97 = t84 &. t14 in
  let t98 = t87 &. t19 in
  let t99 = t83 &. t20 in
  let t100 = t82 &. t10 in
  let t101 = t86 &. t7 in
  let t102 = t81 &. t9 in
  let t103 = t80 &. t22 in
  let t104 = t85 &. t2 in
  let t105 = t88 &. t41 in
  let t106 = t84 &. t16 in
  let t107 = t104 ^. t105 in
  let t108 = t93 ^. t99 in
  let t109 = t96 ^. t107 in
  let t110 = t98 ^. t108 in
  let t111 = t91 ^. t101 in
  let t112 = t89 ^. t92 in
  let t113 = t107 ^. t112 in
  let t114 = t90 ^. t110 in
  let t115 = t89 ^. t95 in
  let t116 = t94 ^. t102 in
  let t117 = t97 ^. t103  in
  let t118 = t91 ^. t114 in
  let t119 = t111 ^. t117 in
  let t120 = t100 ^. t108 in
  let t121 = t92 ^. t95 in
  let t122 = t110 ^. t121 in
  let t123 = t106 ^. t119 in
  let t124 = t104 ^. t115 in
  let t125 = t111 ^. t116 in
  let st7 = t109 ^. t122 in
  let st5 = ~. (t123 ^. t124) in
  let t128 = t94 ^. t107 in
  let st4 = t113 ^. t114 in
  let st3 = t118 ^. t128 in
  let t131 = t93 ^. t101 in
  let t132 = t112 ^. t120 in
  let st0 = ~. (t113 ^. t125) in
  let t134 = t97 ^. t116 in
  let t135 = t131 ^. t134 in
  let t136 = t93 ^. t115 in
  let st1 = ~.(t109 ^. t135) in
  let t138 = t119 ^. t132 in
  let st2 = t109 ^. t138 in
  let t140 = t114 ^. t136 in
  let st6 = ~. (t109 ^. t140) in
    admit();
  (st0,st1,st2,st3,st4,st5,st6,st7)


assume val uploadFirstMaskMC: unit -> u1x16
assume val uploadFirstMaskMCRot: unit -> u1x16

assume val uploadSecondMaskMC: unit -> u1x16 
assume val uploadSecondMaskMCRot: unit -> u1x16


assume val _mixColumn: lseq uint8 16 -> lseq uint8 16

let mix_col64_1 (u: u1x16) = 
  let mask0 = uploadFirstMaskMC () in 
  let mask1 = uploadFirstMaskMCRot () in 
   u ^! (((u &! mask0) >>! size 1) |! ((u &! mask1) <<! size 3))


val mix_col64_1_xn: #n: xN -> a: uint16xN n -> uint16xN n

let mix_col64_1_xn #n a = 
  map mix_col64_1 a


inline_for_extraction
let map3_inner (#a:Type) (#b:Type) (#c:Type) (#d: Type) (#len:size_nat)
  (f:(a -> b ->c ->  Tot d)) (s1:lseq a len) (s2:lseq b len) (s3: lseq c len) (i:size_nat{i < len}) =
  f s1.[i] s2.[i] s3.[i] 


(* more maps for the god of maps *)
val map3:#a:Type -> #b:Type -> #c:Type -> #d: Type ->  #len:size_nat
  -> f:(a -> b -> c -> Tot d)
  -> s1:lseq a len
  -> s2:lseq b len
  -> s3:lseq c len ->
  Tot (s4: lseq d len{(forall (i:nat).
    {:pattern (index s4 i)} i < len ==> index s4 i == f s1.[i] s2.[i] s3.[i])})

let map3 #a #b #c #d #len f s1 s2 s3 =
  createi #d len (map3_inner #a #b #c #d #len f s1 s2 s3)



let mix_col64_2 (prev: u1x16) (next: u1x16) (st: u1x16) = 
  let mask0 = uploadSecondMaskMC () in 
  let mask1 = uploadSecondMaskMCRot() in 
  let ncoli = (((next &! mask0) >>! size  2) |! ((next &! mask1) <<! size  2)) in
  st ^! ncoli ^! prev


val mix_col64_2_xn: #n: xN -> prev: uint16xN n -> next: uint16xN n -> st: uint16xN n -> uint16xN n

let mix_col64_2_xn #n prev next st = 
  map3 mix_col64_2 prev next st

let mix_col64_3 (a: u1x16)  = 
  let mask0 = uploadSecondMaskMC() in 
  let mask1 = uploadSecondMaskMCRot () in 
  a ^! (((a &! mask0) >>! size  2) |! ((a &! mask1) <<! size  2))

val mix_col64_3_xn: #n:xN -> a: uint16xN n -> uint16xN n

let mix_col64_3_xn #n a = 
  map mix_col64_3 a

val mixColumn: #n: xN -> s: state_tuple n -> (r: state_tuple n 
  {
    let transposed = transpose s in 
    let app = map _mixColumn transposed in 
    let inv_transposed = invTranspose app in 
    r == inv_transposed
  }
)

let mixColumn #n (st0, st1, st2, st3, st4, st5, st6, st7) = 
    let mask0 = uploadSecondMaskMC() in 
    let mask1 = uploadSecondMaskMCRot () in 

    let col0 = mix_col64_1_xn st0 in 
    let col1 = mix_col64_1_xn st1 in 
    let col2 = mix_col64_1_xn st2 in 
    let col3 = mix_col64_1_xn st3 in 
    let col4 = mix_col64_1_xn st4 in 
    let col5 = mix_col64_1_xn st5 in 
    let col6 = mix_col64_1_xn st6 in 
    let col7 = mix_col64_1_xn st7 in 

    let ncol0 = mix_col64_3_xn col0 in 
  
    let st0 = st0 ^. ncol0 in 
    let st1 = mix_col64_2_xn col0 col1 st1 in 
    let st2 = mix_col64_2_xn col1 col2 st2 in 
    let st3 = mix_col64_2_xn col2 col3 st3 in 
    let st4 = mix_col64_2_xn col3 col4 st4 in 
    let st5 = mix_col64_2_xn col4 col5 st5 in 
    let st6 = mix_col64_2_xn col5 col6 st6 in 
    let st7 = mix_col64_2_xn col6 col7 st7 in 

    let st0 = st0 ^. col7 in 
    let st1 = st1 ^. col7 in 
    let st3 = st3 ^. col7 in 
    let st4 = st4 ^. col7 in 
    admit();
    (st0, st1, st2, st3, st4, st5, st6, st7)

assume val uploadFirstBitMask: unit -> u1x16
assume val uploadSecondBitMask: unit -> u1x16
assume val uploadSecondBitMaskRot: unit -> u1x16
assume val uploadThirdBitMask: unit -> u1x16 
assume val uploadThirdBitMaskRot: unit -> u1x16
assume val uploadForthBitMask: unit -> u1x16
assume val uploadForthBitMaskRot: unit -> u1x16


val shift_row_u1x6: u: u1x16 -> u1x16

let shift_row_u1x16 u = 
  let mask0 = uploadFirstBitMask () in 
  let mask1 = uploadSecondBitMask () in 
  let mask2 = uploadSecondBitMaskRot () in 
  let mask3 = uploadThirdBitMask () in 
  let mask4 = uploadThirdBitMaskRot() in 
  let mask5 = uploadForthBitMask () in 
  let mask6 = uploadForthBitMaskRot() in 
  let u = (u &! mask0) |! 
    ((u &! mask1) >>! size 4) |!
    ((u &! mask2) <<! size 12) |!
    ((u &! mask3) >>! size 8) |!
    ((u &! mask4) <<! size 8) |!
    ((u &! mask5) <<! size 12) |!
    ((u &! mask6) >>! size 4) in 
  u  

val shiftRow_uint16xN: #n: xN -> uint16xN n -> uint16xN n

let shiftRow_uint16xN #n a =  map shift_row_u1x16 a

assume val _shiftRows: lseq uint8 16 -> lseq uint8 16

val shiftRows: #n: xN -> s: state_tuple n -> (r: state_tuple n {
  let transposed = transpose s in 
  let app = map _shiftRows transposed in 
  let inv_transposed = invTranspose app in 
  r == inv_transposed})

let shiftRows #n (st0, st1, st2, st3, st4, st5, st6, st7) = 
  let st0 = shiftRow_uint16xN st0 in 
  let st1 = shiftRow_uint16xN st1 in 
  let st2 = shiftRow_uint16xN st2 in 
  let st3 = shiftRow_uint16xN st3 in 
  let st4 = shiftRow_uint16xN st4 in 
  let st5 = shiftRow_uint16xN st5 in 
  let st6 = shiftRow_uint16xN st6 in 
  let st7 = shiftRow_uint16xN st7 in 
    admit();
  (st0, st1, st2, st3, st4, st5, st6, st7)



(*

assume val _addRoundKey: key: lseq uint8 16 ->block: lseq uint8 16 ->  lseq uint8 16

assume val addRoundKey: #n: xN -> s: state n -> key: lseq uint8 16 -> (r: state n 
  {
    let transposed = transpose2 s in 
    let app = map (_addRoundKey key) transposed in 
    let inv_transposed = invTranspose2 app in 
    r == inv_transposed
  }
)  

*)
