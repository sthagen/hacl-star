module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Basic

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence


noextract
val fromDomain_: a: int -> Tot (r: nat (*{ r = a * modp_inv2 (pow2 256) % prime256}*))

noextract
val fromDomainPoint: a: tuple3 nat nat nat -> Tot (r: tuple3 nat nat nat 
  {
    let x, y, z = a in
    let x3, y3, z3 = r in 
    x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z
  }
)


noextract
val toDomain_: a: int -> Tot (r: nat (*{r =  a * pow2 256 % prime256}*))

val lemmaFromDomain: a: int -> Lemma (fromDomain_ (a) == a * modp_inv2 (pow2 256) % prime256)

val lemmaToDomain: a: int -> Lemma (toDomain_(a) == a * (pow2 256) % prime256)

val lemmaToDomainAndBackIsTheSame: a: nat { a < prime256} -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

val lemmaFromDomainToDomain: a: nat { a < prime256} -> Lemma (toDomain_ (fromDomain_ a) == a)


val lemmaFromDomainToDomainModuloPrime: a: int -> Lemma (a % prime256 == fromDomain_(toDomain_ a))


(* the lemma shows the equivalence between toDomain(a:nat) and toDomain(a % prime256) *)
val inDomain_mod_is_not_mod: a: int -> Lemma (toDomain_ a == toDomain_ (a % prime256))

val multiplicationInDomainNat: #k: nat -> #l: nat ->
  a: nat {a == toDomain_ k /\ a < prime256} -> 
  b: nat {b == toDomain_ l /\ b < prime256} ->
  Lemma (
    let multResult = a * b * modp_inv2_prime (pow2 256) prime256 % prime256 in 
    multResult == toDomain_ (k * l))

val additionInDomain2Nat: a: nat {a < prime256} -> b: nat {b < prime256} -> Lemma 
  (
    let result = (a + b) % prime256 in 
    result = toDomain_ (fromDomain_ a + fromDomain_ b)
  )
  
val substractionInDomain2Nat: a: nat {a < prime256} -> b: nat { b < prime256} -> Lemma 
  ((a - b) % prime256 == toDomain_ (fromDomain_ a - fromDomain_ b))
  

noextract 
val felem_add_seq: a: felem_seq{felem_seq_as_nat a < prime256} -> b: felem_seq{felem_seq_as_nat b < prime256} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\ 
    felem_seq_as_nat r = toDomain_ ((fromDomain_ (felem_seq_as_nat a) + fromDomain_ (felem_seq_as_nat b)) % prime256)})

noextract
val felem_sub_seq: a: felem_seq{felem_seq_as_nat a < prime256} -> b: felem_seq{felem_seq_as_nat b < prime256} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\ 
  felem_seq_as_nat r = toDomain_ ((fromDomain_ (felem_seq_as_nat a) - fromDomain_(felem_seq_as_nat b))% prime256)})


noextract
val montgomery_multiplication_seq: a: felem_seq {felem_seq_as_nat a < prime256} -> b: felem_seq {felem_seq_as_nat b < prime256} -> Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_(felem_seq_as_nat b) % prime256)
  }) 
   
noextract
val mm_cube_seq: a: felem_seq {felem_seq_as_nat a < prime256}-> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) % prime256) })

noextract
val mm_quatre_seq: a: felem_seq {felem_seq_as_nat a < prime256} -> 
  Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\ 
  felem_seq_as_nat r = toDomain_ (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) % prime256)})

noextract 
val mm_byTwo_seq: a: felem_seq {felem_seq_as_nat a < prime256} -> Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\
  felem_seq_as_nat r = toDomain_ (2 * fromDomain_ (felem_seq_as_nat a) % prime256)})


val lemma_add_same_value_is_by_two: a: felem_seq {felem_seq_as_nat a < prime256} -> 
  Lemma (felem_add_seq a a  == mm_byTwo_seq a)

noextract 
val mm_byThree_seq: a: felem_seq {felem_seq_as_nat a < prime256} -> Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\
  felem_seq_as_nat r = toDomain_ (3 * fromDomain_ (felem_seq_as_nat a) % prime256 )})

noextract 
val mm_byFour_seq: a: felem_seq {felem_seq_as_nat a < prime256} -> Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\
  felem_seq_as_nat r = toDomain_ (4 * fromDomain_ (felem_seq_as_nat a) % prime256)})

noextract 
val mm_byEight_seq: a: felem_seq {felem_seq_as_nat a < prime256} -> Tot (r: felem_seq {felem_seq_as_nat r < prime256 /\
  felem_seq_as_nat r = toDomain_ (8 * fromDomain_ (felem_seq_as_nat a) % prime256)})
