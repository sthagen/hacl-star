module Lib.Exponentiation

open FStar.Mul

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//we don't require to have an inverse element to be an abelian group
//so this is just commutative monoid
inline_for_extraction
class comm_monoid (t:Type) = {
  one: t;
  mul: t -> t -> t;
  lemma_one: a:t -> Lemma (mul a one == a);
  lemma_mul_assoc: a:t -> b:t -> c:t -> Lemma (mul (mul a b) c == mul a (mul b c));
  lemma_mul_comm: a:t -> b:t -> Lemma (mul a b == mul b a)
  }

let sqr (#t:Type) (k:comm_monoid t) (a:t) : t = mul a a

let rec pow (#t:Type) (k:comm_monoid t) (x:t) (n:nat) : t =
  if n = 0 then one
  else mul x (pow k x (n - 1))


val lemma_pow0: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 0 == one)

val lemma_pow1: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 1 == x)

val lemma_pow_unfold: #t:Type -> k:comm_monoid t -> x:t -> n:pos ->
  Lemma (mul x (pow k x (n - 1)) == pow k x n)

val lemma_pow_one: #t:Type -> k:comm_monoid t -> n:nat -> Lemma (pow k one n == one)

val lemma_pow_add: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat ->
  Lemma (mul (pow k x n) (pow k x m) == pow k x (n + m))

val lemma_pow_mul: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat ->
  Lemma (pow k (pow k x n) m == pow k x (n * m))

val lemma_pow_double: #t:Type -> k:comm_monoid t -> x:t -> b:nat ->
  Lemma (pow k (mul x x) b == pow k x (b + b))

val lemma_pow_mul_base: #t:Type -> k:comm_monoid t -> a:t -> b:t -> n:nat ->
  Lemma (mul (pow k a n) (pow k b n) == pow k (mul a b) n)


//a right-to-left binary method
let exp_rl_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((a, acc) : tuple2 t t) : tuple2 t t =
  let acc = if (b / pow2 i % 2 = 1) then mul acc a else acc in
  let a = mul a a in
  (a, acc)

let exp_rl (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (a, acc) = Loops.repeati bBits (exp_rl_f k bBits b) (a, one) in
  acc

val exp_rl_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_rl k a bBits b == pow k a b)


//a left-to-right binary method
let exp_lr_f (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) (acc:t) : t =
  let acc = mul acc acc  in
  let acc = if (b / pow2 (bBits - i - 1) % 2 = 0) then acc else mul acc a in
  acc

let exp_lr (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  Loops.repeati bBits (exp_lr_f k a bBits b) one

val exp_lr_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_lr k a bBits b == pow k a b)


// Montgomery ladder for exponentiation
let exp_mont_ladder_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((r0, r1) : tuple2 t t) : tuple2 t t =
  if (b / pow2 (bBits - i - 1) % 2 = 0) then
    (mul r0 r0, mul r1 r0)
  else
    (mul r0 r1, mul r1 r1)

let exp_mont_ladder (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (r0, r1) = Loops.repeati bBits (exp_mont_ladder_f k bBits b) (one, a) in
  r0

val exp_mont_ladder_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder k a bBits b == pow k a b)


// Montgomery ladder for exponentiation with cswap
let cswap (#t:Type) (sw:nat) (r0:t) (r1:t) : tuple2 t t =
  if sw = 1 then (r1, r0) else (r0, r1)

// cswap -> step -> cswap -> cswap -> step -> cswap -> ..
let exp_mont_ladder_swap2_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((r0, r1) : tuple2 t t) : tuple2 t t =
  let bit = b / pow2 (bBits - i - 1) % 2 in
  let r0, r1 = cswap bit r0 r1 in
  let r0, r1 = (mul r0 r0, mul r1 r0) in
  let r0, r1 = cswap bit r0 r1 in
  (r0, r1)

let exp_mont_ladder_swap2 (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (r0, r1) = Loops.repeati bBits (exp_mont_ladder_swap2_f k bBits b) (one, a) in
  r0

val exp_mont_ladder_swap2_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder_swap2 k a bBits b == exp_mont_ladder k a bBits b)


// cswap -> step -> cswap -> step -> cswap -> ..
let exp_mont_ladder_swap_f (#t:Type) (k:comm_monoid t) (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) ((r0, r1, privbit) : tuple3 t t nat) : tuple3 t t nat =
  let bit = b / pow2 (bBits - i - 1) % 2 in
  let sw = (bit + privbit) % 2 in
  let r0, r1 = cswap sw r0 r1 in
  let r0, r1 = (mul r0 r0, mul r1 r0) in
  (r0, r1, bit)

let exp_mont_ladder_swap (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let r0 = one in
  let r1 = a in
  let sw = 0 in
  let (r0', r1', sw') = Loops.repeati bBits (exp_mont_ladder_swap_f k bBits b) (r0, r1, sw) in
  let r0', r1' = cswap sw' r0' r1' in
  r0'

val exp_mont_ladder_swap_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder_swap k a bBits b == exp_mont_ladder k a bBits b)


// a fixed window method
let exp_pow2 (#t:Type) (k:comm_monoid t) (a:t) (b:nat) : t =
  Loops.repeat b (sqr k) a

val exp_pow2_lemma: #t:Type -> k:comm_monoid t -> a:t -> b:nat ->
  Lemma (exp_pow2 k a b == pow k a (pow2 b))


let get_bits_l (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) : r:nat{r < pow2 l} =
  Math.Lemmas.lemma_mult_le_left l (i + 1) (bBits / l);
  assert (l * (i + 1) <= l * (bBits / l));
  Math.Lemmas.multiply_fractions bBits l;
  assert (l * (i + 1) <= bBits);
  b / pow2 (bBits - l * i - l) % pow2 l


let get_bits_c (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) : r:nat{r < pow2 l} =
  let c = bBits % l in
  let bits_c = b % pow2 c in
  Math.Lemmas.pow2_lt_compat l c;
  bits_c


let mul_acc_pow_a_bits_l (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) (acc:t) : t =
  let bits_l = get_bits_l bBits b l i in
  mul acc (pow k a bits_l)

let mul_acc_pow_a_bits_c (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (acc:t) : t =
  let bits_c = get_bits_c bBits b l in
  mul acc (pow k a bits_c)


// mul (pow k acc (pow2 l)) (pow k a (b / pow2 (bBits - l * i - l) % pow2 l))
let exp_fw_f (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) (acc:t) : t =
  let acc1 = exp_pow2 k acc l in
  mul_acc_pow_a_bits_l k a bBits b l i acc1


// mul (pow k acc (pow2 c)) (pow k a (b % pow2 c))
let exp_fw_rem (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (acc:t) : t =
  let c = bBits % l in
  let acc1 = exp_pow2 k acc c in
  mul_acc_pow_a_bits_c k a bBits b l acc1


let exp_fw (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) : t =
  let acc = Loops.repeati (bBits / l) (exp_fw_f k a bBits b l) one in
  let res = if bBits % l = 0 then acc else exp_fw_rem k a bBits b l acc in
  res

val exp_fw_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos ->
  Lemma (exp_fw k a bBits b l == pow k a b)


// double exponentiation
let exp_double_fw_f (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (l:pos) (i:nat{i < bBits / l}) (acc:t) : t
 =
  let acc1 = exp_fw_f k a1 bBits b1 l i acc in
  mul_acc_pow_a_bits_l k a2 bBits b2 l i acc1


let exp_double_fw_rem (#t:Type) (k:comm_monoid t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (l:pos) (acc:t) : t
 =
  let acc1 = exp_fw_rem k a1 bBits b1 l acc in
  mul_acc_pow_a_bits_c k a2 bBits b2 l acc1


let exp_double_fw (#t:Type) (k:comm_monoid t) (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits}) (a2:t) (b2:nat{b2 < pow2 bBits}) (l:pos) : t =
  let acc = Loops.repeati (bBits / l) (exp_double_fw_f k a1 bBits b1 a2 b2 l) one in
  let res = if bBits % l = 0 then acc else exp_double_fw_rem k a1 bBits b1 a2 b2 l acc in
  res


val exp_double_fw_lemma: #t:Type -> k:comm_monoid t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos ->
  Lemma (exp_double_fw k a1 bBits b1 a2 b2 l == mul (pow k a1 b1) (pow k a2 b2))
