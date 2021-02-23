module Hacl.EC.Ed25519

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module F51 = Hacl.Impl.Ed25519.Field51
module SE = Spec.Ed25519
module SC = Spec.Curve25519


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//
// Finite field arithmetic
//

val mk_felem_zero: b:F51.felem ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.mul_inv_t h1 b /\
    F51.fevalh h1 b == SC.zero)

let mk_felem_zero b =
  Hacl.Bignum25519.make_zero b


val mk_felem_one: b:F51.felem ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.mul_inv_t h1 b /\
    F51.fevalh h1 b == SC.one)

let mk_felem_one b =
  Hacl.Bignum25519.make_one b


val felem_add: a:F51.felem -> b:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    (disjoint out a \/ out == a) /\
    (disjoint out b \/ out == b) /\
    (disjoint a b \/ a == b) /\
    F51.mul_inv_t h a /\
    F51.mul_inv_t h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fadd (F51.fevalh h0 a) (F51.fevalh h0 b))

let felem_add a b out =
  Hacl.Impl.Curve25519.Field51.fadd out a b;
  Hacl.Bignum25519.reduce_513 out


val felem_sub: a:F51.felem -> b:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    (disjoint out a \/ out == a) /\
    (disjoint out b \/ out == b) /\
    (disjoint a b \/ a == b) /\
    F51.mul_inv_t h a /\
    F51.mul_inv_t h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fsub (F51.fevalh h0 a) (F51.fevalh h0 b))

let felem_sub a b out =
  Hacl.Impl.Curve25519.Field51.fsub out a b;
  Hacl.Bignum25519.reduce_513 out


val felem_mul: a:F51.felem -> b:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    F51.mul_inv_t h a /\
    F51.mul_inv_t h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fmul (F51.fevalh h0 a) (F51.fevalh h0 b))

let felem_mul a b out =
  push_frame();
  let tmp = create 10ul (u128 0) in
  Hacl.Impl.Curve25519.Field51.fmul out a b tmp;
  pop_frame()


val felem_inv: a:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out /\
    F51.mul_inv_t h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SE.modp_inv (F51.fevalh h0 a))

let felem_inv a out =
  Hacl.Bignum25519.inverse out a;
  Hacl.Bignum25519.reduce_513 out


val felem_load: b:lbuffer uint8 32ul -> out:F51.felem ->
  Stack unit
  (requires fun h -> live h b /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.as_nat h1 out == Lib.ByteSequence.nat_from_bytes_le (as_seq h0 b) % pow2 255)

let felem_load b out =
  Hacl.Bignum25519.load_51 out b


val felem_store: a:F51.felem -> out:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h out /\
    F51.mul_inv_t h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Lib.ByteSequence.nat_to_bytes_le 32 (F51.fevalh h0 a))

let felem_store a out =
  Hacl.Bignum25519.store_51 out a

//
// Elliptic curve operations
//
val mk_point_at_inf: p:F51.point ->
  Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    F51.point_inv_t h1 p /\
    F51.point_eval h1 p == SC.(zero, one, one, zero))

let mk_point_at_inf p =
  Hacl.Impl.Ed25519.Ladder.make_point_inf p


val mk_base_point: p:F51.point ->
  Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    F51.point_inv_t h1 p /\
    F51.point_eval h1 p == SE.g)

let mk_base_point p =
  Hacl.Impl.Ed25519.Ladder.make_g p


val point_negate: p:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\ disjoint out p /\
    F51.point_inv_t h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
   (let (x1, y1, z1, t1) = F51.point_eval h0 p in
    F51.point_inv_t h1 out /\
    F51.point_eval h1 out == SC.((-x1) % prime, y1, z1, (-t1) % prime)))

let point_negate p out =
  push_frame ();
  let zero = create 5ul (u64 0) in
  Hacl.Bignum25519.make_zero zero;
  let x = sub p 0ul 5ul in
  let y = sub p 5ul 5ul in
  let z = sub p 10ul 5ul in
  let t = sub p 15ul 5ul in

  let x1 = sub out 0ul 5ul in
  let y1 = sub out 5ul 5ul in
  let z1 = sub out 10ul 5ul in
  let t1 = sub out 15ul 5ul in

  copy x1 x;
  Hacl.Bignum25519.fdifference x1 zero;
  Hacl.Bignum25519.reduce_513 x1;
  copy y1 y;
  copy z1 z;
  copy t1 t;
  Hacl.Bignum25519.fdifference t1 zero;
  Hacl.Bignum25519.reduce_513 t1;
  pop_frame()


val point_add: p:F51.point -> q:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\
    disjoint p out /\ disjoint q out /\
    F51.point_inv_t h p /\ F51.point_inv_t h q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\
    F51.point_eval h1 out == SE.point_add (F51.point_eval h0 p) (F51.point_eval h0 q))

let point_add p q out =
  Hacl.Impl.Ed25519.PointAdd.point_add out p q


val point_mul: scalar:lbuffer uint8 32ul -> p:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h p /\ live h out /\
    F51.point_inv_t h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\
    F51.point_eval h1 out == SE.point_mul (as_seq h0 scalar) (F51.point_eval h0 p))

let point_mul scalar p out =
  Hacl.Impl.Ed25519.Ladder.point_mul out scalar p


val point_eq: p:F51.point -> q:F51.point ->
  Stack bool
  (requires fun h ->
    live h p /\ live h q /\
    F51.point_inv_t h p /\ F51.point_inv_t h q)
  (ensures  fun h0 z h1 -> modifies0 h0 h1 /\
    (z <==> SE.point_equal (F51.point_eval h0 p) (F51.point_eval h0 q)))

let point_eq p q =
  Hacl.Impl.Ed25519.PointEqual.point_equal p q


val point_compress: p:F51.point -> out:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\
    F51.point_inv_t h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == SE.point_compress (F51.point_eval h0 p))

let point_compress p out =
  Hacl.Impl.Ed25519.PointCompress.point_compress out p


val point_decompress: s:lbuffer uint8 32ul -> out:F51.point ->
  Stack bool
  (requires fun h ->
    live h out /\ live h s /\
    F51.point_inv_t h out)
  (ensures  fun h0 b h1 -> modifies (loc out) h0 h1 /\
    (b ==> F51.point_inv_t h1 out) /\
    (b <==> Some? (SE.point_decompress (as_seq h0 s))) /\
    (b ==> (F51.point_eval h1 out == Some?.v (SE.point_decompress (as_seq h0 s)))))

let point_decompress s out =
  Hacl.Impl.Ed25519.PointDecompress.point_decompress out s
