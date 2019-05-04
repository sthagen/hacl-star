module Hacl.Spec.AES_128.BitSlice

open Lib.IntTypes



open Lib.Sequence

val tupleToSeq: t: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) ->Tot (s: Seq.lseq uint64 8{
  let (t0, t1, t2, t3, t4, t5, t6, t7) = t in 
  index #_ #8 s 0   == t0 /\index #_ #8 s 1  == t1 /\ index #_ #8 s 2  == t2 /\ index #_ #8 s 3 == t3 /\ index #_ #8 s 4 == t4 /\ index #_ #8 s 5 == t5 /\ index #_ #8 s 6 == t6 /\ index #_ #8 s 7 == t7})

let tupleToSeq (t0, t1, t2, t3, t4, t5, t6, t7) = 
  let s = Lib.Sequence.create 8 (u64 0) in 
  let s = upd s 0 t0 in 
  let s = upd s 1 t1 in
  let s = upd s 2 t2 in
  let s = upd s 3 t3 in
  let s = upd s 4 t4 in
  let s = upd s 5 t5 in
  let s = upd s 6 t6 in 
  upd s 7 t7
  

val seqToTuple: s: lseq uint64 8 -> Tot (t: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) 
  {  let (t0, t1, t2, t3, t4, t5, t6, t7) = t in 
  index #_ #8 s 0   == t0 /\index #_ #8 s 1  == t1 /\ index #_ #8 s 2  == t2 /\ index #_ #8 s 3 == t3 /\ index #_ #8 s 4 == t4 /\ index #_ #8 s 5 == t5 /\ index #_ #8 s 6 == t6 /\ index #_ #8 s 7 == t7
  })

let seqToTuple s = 
  let s0 = index s 0 in 
  let s1 = index s 1 in 
  let s2 = index s 2 in 
  let s3 = index s 3 in 
  let s4 = index s 4 in 
  let s5 = index s 5 in 
  let s6 = index s 6 in 
  let s7 = index s 7 in 
  (s0, s1, s2, s3, s4, s5, s6, s7)

assume val tuple8ToBlock4: t: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)  -> Hacl.Spec.AES.block4
assume val seqToBlock4: s: lseq uint64 8 -> Hacl.Spec.AES.block4
assume val lemmaSeqToTupleToBlock: a: lseq uint64 8 -> Lemma (tuple8ToBlock4 (seqToTuple a) == seqToBlock4 a)







let transpose_bits64 (x:uint64) : Tot uint64 =
  (x &. u64 0x8040201008040201)    |.
  ((x &. u64 0x4020100804020100) >>. size 7) |.
  ((x &. u64 0x2010080402010000) >>. size 14) |.
  ((x &. u64 0x1008040201000000) >>. size 21) |.
  ((x &. u64 0x0804020100000000) >>. size 28) |.
  ((x &. u64 0x0402010000000000) >>. size 35) |.
  ((x &. u64 0x0201000000000000) >>. size 42) |.
  ((x &. u64 0x0100000000000000) >>. size 49) |.
  ((x <<. size  7) &. u64 0x4020100804020100) |.
  ((x <<. size 14) &. u64 0x2010080402010000) |.
  ((x <<. size 21) &. u64 0x1008040201000000) |.
  ((x <<. size 28) &. u64 0x0804020100000000) |.
  ((x <<. size 35) &. u64 0x0402010000000000) |.
  ((x <<. size 42) &. u64 0x0201000000000000) |.
  ((x <<. size 49) &. u64 0x0100000000000000)


inline_for_extraction
val transpose_bits64x8: i: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) -> 
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let transpose_bits64x8 (i0, i1, i2, i3, i4, i5, i6, i7) =
  let t0 = (i0 &. u64 0xffffffff) ^. (i4 <<. size 32) in
  let t1 = (i1 &. u64 0xffffffff) ^. (i5 <<. size 32) in
  let t2 = (i2 &. u64 0xffffffff) ^. (i6 <<. size 32) in
  let t3 = (i3 &. u64 0xffffffff) ^. (i7 <<. size 32) in
  let t4 = (i4 &. u64 0xffffffff00000000) ^. (i0 >>. size  32) in
  let t5 = (i5 &. u64 0xffffffff00000000) ^. (i1 >>. size  32) in
  let t6 = (i6 &. u64 0xffffffff00000000) ^. (i2 >>. size  32) in
  let t7 = (i7 &. u64 0xffffffff00000000) ^. (i3 >>. size  32) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t3 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in

  let t0 = (t0 &. u64 0x0000ffff0000ffff) ^. ((t2 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t1 = (t1 &. u64 0x0000ffff0000ffff) ^. ((t3 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t2 = (t2 &. u64 0xffff0000ffff0000) ^. ((t0_ &. u64 0xffff0000ffff0000) >>. size  16) in
  let t3 = (t3 &. u64 0xffff0000ffff0000) ^. ((t1_ &. u64 0xffff0000ffff0000) >>. size  16) in
  let t4 = (t4 &. u64 0x0000ffff0000ffff) ^. ((t6 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t5 = (t5 &. u64 0x0000ffff0000ffff) ^. ((t7 &. u64 0x0000ffff0000ffff) <<. size 16) in
  let t6 = (t6 &. u64 0xffff0000ffff0000) ^. ((t4_ &. u64 0xffff0000ffff0000) >>. size  16) in
  let t7 = (t7 &. u64 0xffff0000ffff0000) ^. ((t5_ &. u64 0xffff0000ffff0000) >>. size  16) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t2 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in

  let t0 = (t0 &. u64 0x00ff00ff00ff00ff) ^. ((t1 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t1 = (t1 &. u64 0xff00ff00ff00ff00) ^. ((t0_ &. u64 0xff00ff00ff00ff00) >>. size  8) in
  let t2 = (t2 &. u64 0x00ff00ff00ff00ff) ^. ((t3 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t3 = (t3 &. u64 0xff00ff00ff00ff00) ^. ((t2_ &. u64 0xff00ff00ff00ff00) >>. size  8) in
  let t4 = (t4 &. u64 0x00ff00ff00ff00ff) ^. ((t5 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t5 = (t5 &. u64 0xff00ff00ff00ff00) ^. ((t4_ &. u64 0xff00ff00ff00ff00) >>. size  8) in
  let t6 = (t6 &. u64 0x00ff00ff00ff00ff) ^. ((t7 &. u64 0x00ff00ff00ff00ff) <<. size 8) in
  let t7 = (t7 &. u64 0xff00ff00ff00ff00) ^. ((t6_ &. u64 0xff00ff00ff00ff00) >>. size  8) in

  let t0 = transpose_bits64(t0) in
  let t1 = transpose_bits64(t1) in
  let t2 = transpose_bits64(t2) in
  let t3 = transpose_bits64(t3) in
  let t4 = transpose_bits64(t4) in
  let t5 = transpose_bits64(t5) in
  let t6 = transpose_bits64(t6) in
  let t7 = transpose_bits64(t7) in

  (t0,t1,t2,t3,t4,t5,t6,t7)


inline_for_extraction
val sub_bytes64x8: state: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) ->
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let sub_bytes64x8 (st0, st1, st2, st3, st4, st5, st6, st7) =
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
  let st5 = lognot (t123 ^. t124) in
  let t128 = t94 ^. t107 in
  let st4 = t113 ^. t114 in
  let st3 = t118 ^. t128 in
  let t131 = t93 ^. t101 in
  let t132 = t112 ^. t120 in
  let st0 = lognot (t113 ^. t125) in
  let t134 = t97 ^. t116 in
  let t135 = t131 ^. t134 in
  let t136 = t93 ^. t115 in
  let st1 = lognot (t109 ^. t135) in
  let t138 = t119 ^. t132 in
  let st2 = t109 ^. t138 in
  let t140 = t114 ^. t136 in
  let st6 = lognot (t109 ^. t140) in
  (st0,st1,st2,st3,st4,st5,st6,st7)


open Lib.Sequence
type state_seq = lseq uint64 8

val sub_bytes_state_as_seq: st: state_seq -> Tot (r: state_seq {
  Lib.ByteSequence.uints_to_bytes_le r == Hacl.Spec.AES.subBytes (Lib.ByteSequence.uints_to_bytes_le st)})

let sub_bytes_state_as_seq st =
  admit();
   let (st0,st1,st2,st3,st4,st5,st6,st7) = sub_bytes64x8 (st.[0], st.[1], st.[2], st.[3],st.[4], st.[5], st.[6], st.[7])
  in
  let st = upd st 0 st0 in 
  let st = upd st 1 st1 in   
  let st = upd st 2 st2 in 
  let st = upd st 3 st3 in 
  let st = upd st 4 st4 in 
  let st = upd st 5 st5 in 
  let st = upd st 6 st6 in 
  upd st 7 st7


inline_for_extraction
let shift_row64 (u:uint64) =
  let u = (u &. u64 0x1111111111111111) |.
          ((u &. u64 0x2220222022202220) >>. size 4) |.
          ((u &. u64 0x0002000200020002) <<. size 12) |.
          ((u &. u64 0x4400440044004400) >>. size 8) |.
          ((u &. u64 0x0044004400440044) <<. size 8) |.
          ((u &. u64 0x8000800080008000) >>. size 12) |.
          ((u &. u64 0x0888088808880888) <<. size 4) in
  u

inline_for_extraction
val shift_row_state_s: state: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) -> Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) 

let shift_row_state_s (st0, st1, st2, st3, st4, st5, st6, st7) = 
  let st0 = shift_row64 st0 in 
  let st1 = shift_row64 st1 in 
  let st2 = shift_row64 st2 in 
  let st3 = shift_row64 st3 in 
  let st4 = shift_row64 st4 in 
  let st5 = shift_row64 st5 in 
  let st6 = shift_row64 st6 in 
  let st7 = shift_row64 st7 in 
  (st0, st1, st2, st3, st4, st5, st6, st7)
  

val shift_row_state_as_seq:  st: state_seq -> (r: state_seq 
  {
    Lib.ByteSequence.uints_to_bytes_le r == Hacl.Spec.AES.shiftRows (Lib.ByteSequence.uints_to_bytes_le st)
  }
 )

let shift_row_state_as_seq st = 
  admit();
  let (st0,st1,st2,st3,st4,st5,st6,st7) = shift_row_state_s (st.[0], st.[1], st.[2], st.[3],st.[4], st.[5], st.[6], st.[7]) in
  let st = upd st 0 st0 in 
  let st = upd st 1 st1 in   
  let st = upd st 2 st2 in 
  let st = upd st 3 st3 in 
  let st = upd st 4 st4 in 
  let st = upd st 5 st5 in 
  let st = upd st 6 st6 in 
  upd st 7 st7



inline_for_extraction 
let mix_col64_1 (u: uint64) = 
   u ^. (((u &. u64 0xeeeeeeeeeeeeeeee) >>. size 1)
   |. ((u &. u64 0x1111111111111111) <<. size 3))

inline_for_extraction
let mix_col64_2 (prev: uint64) (next : uint64) (st : uint64) =
  let ncoli = next ^. (((next &. u64 0xcccccccccccccccc ) >>. size  2) |. ((next &. u64 0x3333333333333333) <<. size  2)) in
  st ^. ncoli ^. prev
  
inline_for_extraction
val mix_col64x8 : (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) ->
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let mix_col64x8 (st0, st1, st2, st3, st4, st5, st6, st7) = 
  let col0 = mix_col64_1 st0 in 
  let col1 = mix_col64_1 st1 in 
  let col2 = mix_col64_1 st2 in 
  let col3 = mix_col64_1 st3 in 
  let col4 = mix_col64_1 st4 in 
  let col5 = mix_col64_1 st5 in 
  let col6 = mix_col64_1 st6 in 
  let col7 = mix_col64_1 st7 in 

  let ncol0 = col0 ^. (((col0 &. u64 0xcccccccccccccccc ) >>. size  2) |. ((col0 &. u64 0x3333333333333333) <<. size  2)) in 
  
  let st0 = st0 ^. ncol0 in 
  let st1 = mix_col64_2 col0 col1 st1 in 
  let st2 = mix_col64_2 col1 col2 st2 in 
  let st3 = mix_col64_2 col2 col3 st3 in 
  let st4 = mix_col64_2 col3 col4 st4 in 
  let st5 = mix_col64_2 col4 col5 st5 in 
  let st6 = mix_col64_2 col5 col6 st6 in 
  let st7 = mix_col64_2 col6 col7 st7 in 

  let st0 = st0 ^. col7 in 
  let st1 = st1 ^. col7 in 
  let st3 = st3 ^. col7 in 
  let st4 = st4 ^. col7 in 
  (st0, st1, st2, st3, st4, st5, st6, st7)


val mix_col64_as_seq: st: state_seq -> state_seq 

let mix_col64_as_seq st = 
  let (st0, st1, st2, st3, st4, st5, st6, st7) =  mix_col64x8 (st.[0], st.[1], st.[2], st.[3],st.[4], st.[5], st.[6], st.[7])  in
  let st = upd st 0 st0 in 
  let st = upd st 1 st1 in   
  let st = upd st 2 st2 in 
  let st = upd st 3 st3 in 
  let st = upd st 4 st4 in 
  let st = upd st 5 st5 in 
  let st = upd st 6 st6 in 
  upd st 7 st7



val aes_key_assisti_s: rcon: uint8 -> i: shiftval U8 -> u: uint64 -> Tot uint64 

let aes_key_assisti_s rcon i u = 
  let n = (u &. u64 0xf000f000f000f000) >>. size 12 in
  let n = ((n >>. size 1) |. (n <<. size 3)) &. u64  0x000f000f000f000f in
  let ri = to_u64 ((rcon >>. i) &. u8 1) in
  let ri = ri ^. (ri <<. size 16) in
  let ri = ri ^. (ri <<. size 32) in
  let n = n ^. ri in
  let n = n <<. size 12 in
  n

inline_for_extraction
val aes_key_assist_s: prev:(uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) ->  rcon: uint8 ->   Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let aes_key_assist_s (prev0, prev1, prev2, prev3, prev4, prev5, prev6, prev7) rcon = 
  let (next0, next1, next2, next3, next4, next5, next6, next7) = sub_bytes64x8 (prev0, prev1, prev2, prev3, prev4, prev5, prev6, prev7) in 
  let next0 = aes_key_assisti_s rcon (size 0) next0 in 
  let next1 = aes_key_assisti_s rcon (size 1)  next1 in 
  let next2 = aes_key_assisti_s rcon (size 2)  next2 in 
  let next3 = aes_key_assisti_s rcon (size 3)  next3 in 
  let next4 = aes_key_assisti_s rcon (size 4)  next4 in 
  let next5 = aes_key_assisti_s rcon (size 5)  next5 in 
  let next6 = aes_key_assisti_s rcon (size 6)  next6 in 
  let next7 = aes_key_assisti_s rcon (size 7) next7 in 
  (next0, next1, next2, next3, next4, next5, next6, next7)
  

val aes_key_assist_as_seq: prev: state_seq -> rcon : uint8 -> state_seq 

let aes_key_assist_as_seq prev rcon = 
  let (next0, next1, next2, next3, next4, next5, next6, next7)  =  
    aes_key_assist_s (prev.[0], prev.[1], prev.[2], prev.[3], prev.[4], prev.[5], prev.[6], prev.[7]) rcon in 
  tupleToSeq ((next0, next1, next2, next3, next4, next5, next6, next7)) 


inline_for_extraction
let key_expand1_s (p: uint64) (n: uint64) : uint64 = 
  let n = (n &. u64 0xf000f000f000f000) in
  let n = n ^. (n >>. size 4) in
  let n = n ^. (n >>. size 8) in
  let p = p ^. ((p &. u64 0x0fff0fff0fff0fff) <<. size 4) ^. ((p &. u64 0x00ff00ff00ff00ff) <<. size 8)
            ^. ((p &. u64 0x000f000f000f000f) <<. size 12) in 
  n ^. p


inline_for_extraction
val key_expansion_step_s:  prev: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)  ->
  next:  (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)  ->  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let key_expansion_step_s (prev0, prev1, prev2, prev3, prev4, prev5, prev6, prev7) (next0, next1, next2, next3, next4, next5, next6, next7) = 
  let next0 = key_expand1_s prev0 next0 in 
  let next1 = key_expand1_s prev1 next1 in 
  let next2 = key_expand1_s prev2 next2 in 
  let next3 = key_expand1_s prev3 next3 in 
  let next4 = key_expand1_s prev4 next4 in 
  let next5 = key_expand1_s prev5 next5 in 
  let next6 = key_expand1_s prev6 next6 in 
  let next7 = key_expand1_s prev7 next7 in 
  (next0, next1, next2, next3, next4, next5, next6, next7)


val key_expansion_step_as_seq: prev: state_seq -> next: state_seq -> state_seq

let key_expansion_step_as_seq prev next = 
  let (next0, next1, next2, next3, next4, next5, next6, next7) = key_expansion_step_s (seqToTuple prev) (seqToTuple next) in 
  tupleToSeq ((next0, next1, next2, next3, next4, next5, next6, next7))


inline_for_extraction
val xor_state_s: st: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) -> ost: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64) -> 
Tot (t: (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)
  {
    let st0 = tuple8ToBlock4 t in 
    let ost0 = tuple8ToBlock4 t in 
    let t0 = tuple8ToBlock4 t in 
    t0 == Hacl.Spec.AES.xor_block st0 ost0
  }
)

let  xor_state_s(st0, st1, st2, st3, st4, st5, st6, st7) (ost0, ost1, ost2, ost3, ost4, ost5, ost6, ost7) = 
  let st0 = st0 ^. ost0 in 
  let st1 = st1 ^. ost1 in 
  let st2 = st2 ^. ost2 in 
  let st3 = st3 ^. ost3 in 
  let st4 = st4 ^. ost4 in 
  let st5 = st5 ^. ost5 in 
  let st6 = st6 ^. ost6 in 
  let st7 = st7 ^. ost7 in 
  admit();
  (st0, st1, st2, st3, st4, st5, st6, st7)


val xor_state_as_seq: st: state_seq -> ost: state_seq -> Tot (r: state_seq
  {
    Lib.ByteSequence.uints_to_bytes_le r == Hacl.Spec.AES.xor_block (Lib.ByteSequence.uints_to_bytes_le st) (Lib.ByteSequence.uints_to_bytes_le ost)
  }
)  
    

let xor_state_as_seq st ost = 
  admit();
  let (st0,st1,st2,st3,st4,st5,st6,st7) = xor_state_s (st.[0], st.[1], st.[2], st.[3],st.[4], st.[5], st.[6], st.[7])
     (ost.[0], ost.[1], ost.[2], ost.[3], ost.[4], ost.[5], ost.[6], ost.[7])
  in
  let st = upd st 0 st0 in 
  let st = upd st 1 st1 in   
  let st = upd st 2 st2 in 
  let st = upd st 3 st3 in 
  let st = upd st 4 st4 in 
  let st = upd st 5 st5 in 
  let st = upd st 6 st6 in 
  upd st 7 st7


val aes_enc_s: state: lseq uint64 8 -> key: lseq uint64 8 -> Tot (r: lseq uint64 8
    {
      Lib.ByteSequence.uints_to_bytes_le r == Hacl.Spec.AES.aes_enc (Lib.ByteSequence.uints_to_bytes_le state) (Lib.ByteSequence.uints_to_bytes_le key)})


let aes_enc_s state key =
  let (st0, st1, st2, st3, st4, st5, st6, st7) = seqToTuple state in 
  let (k0, k1, k2, k3, k4, k5, k6, k7) = seqToTuple key in 

   let  (st0,st1,st2,st3,st4,st5,st6,st7) = sub_bytes64x8 (st0,st1,st2,st3,st4,st5,st6,st7) in 
   let  (st0,st1,st2,st3,st4,st5,st6,st7) = shift_row_state_s (st0,st1,st2,st3,st4,st5,st6,st7) in 
   let  (st0,st1,st2,st3,st4,st5,st6,st7) = mix_col64x8 (st0,st1,st2,st3,st4,st5,st6,st7) in 
   let  (st0,st1,st2,st3,st4,st5,st6,st7) = xor_state_s (st0,st1,st2,st3,st4,st5,st6,st7) (k0, k1, k2, k3, k4, k5, k6, k7) in 

   admit();
   tupleToSeq (st0,st1,st2,st3,st4,st5,st6,st7)


val aes_enc_last_s: state: lseq uint64 8 -> key: lseq uint64 8 -> Tot (r: lseq uint64 8
    {
      Lib.ByteSequence.uints_to_bytes_le r == Hacl.Spec.AES.aes_enc_last (Lib.ByteSequence.uints_to_bytes_le state) (Lib.ByteSequence.uints_to_bytes_le key)})


let aes_enc_last_s state key =   
  let (st0, st1, st2, st3, st4, st5, st6, st7) = seqToTuple state in 
  let (k0, k1, k2, k3, k4, k5, k6, k7) = seqToTuple key in 

  let  (st0,st1,st2,st3,st4,st5,st6,st7) = sub_bytes64x8 (st0,st1,st2,st3,st4,st5,st6,st7) in 
  let  (st0,st1,st2,st3,st4,st5,st6,st7) = shift_row_state_s (st0,st1,st2,st3,st4,st5,st6,st7) in 
  let  (st0,st1,st2,st3,st4,st5,st6,st7) = xor_state_s (st0,st1,st2,st3,st4,st5,st6,st7) (k0, k1, k2, k3, k4, k5, k6, k7) in 
  
  admit();
  tupleToSeq (st0,st1,st2,st3,st4,st5,st6,st7)
