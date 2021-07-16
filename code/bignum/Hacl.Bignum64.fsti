module Hacl.Bignum64

open FStar.Mul

module BN = Hacl.Bignum
module BS = Hacl.Bignum.SafeAPI
module MA = Hacl.Bignum.MontArithmetic

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U64

inline_for_extraction noextract
let lbignum = Hacl.Bignum.Definitions.lbignum

let pbn_mont_ctx_u64 = MA.pbn_mont_ctx_u64

[@@ CPrologue
"/*******************************************************************************

A verified bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of `len` unsigned 64-bit integers, i.e. uint64_t[len].

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/\n";
Comment
"Write `a + b mod 2 ^ (64 * len)` in `res`.

  This functions returns the carry.

  The arguments a, b and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len]"]
val add: len:BN.meta_len t_limbs -> BN.bn_add_eq_len_st t_limbs len

[@@ Comment "Write `a - b mod 2 ^ (64 * len)` in `res`.

  This functions returns the carry.

  The arguments a, b and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len]"]
val sub: len:BN.meta_len t_limbs -> BN.bn_sub_eq_len_st t_limbs len

[@@ Comment "Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n"]
val add_mod: len:BN.meta_len t_limbs -> BN.bn_add_mod_n_st t_limbs len

[@@ Comment "Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n"]
val sub_mod: len:BN.meta_len t_limbs -> BN.bn_sub_mod_n_st t_limbs len

[@@ Comment "Write `a * b` in `res`.

  The arguments a and b are meant to be `len` limbs in size, i.e. uint64_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint64_t[2*len]."]
val mul: len:BN.meta_len t_limbs -> a:lbignum t_limbs len -> BN.bn_karatsuba_mul_st t_limbs len a

[@@ Comment "Write `a * a` in `res`.

  The argument a is meant to be `len` limbs in size, i.e. uint64_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint64_t[2*len]."]
val sqr: len:BN.meta_len t_limbs -> a:lbignum t_limbs len -> BN.bn_karatsuba_sqr_st t_limbs len a

[@@ Comment "Write `a mod n` in `res`.

  The argument a is meant to be `2*len` limbs in size, i.e. uint64_t[2*len].
  The argument n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1 "]
val mod: len:BN.meta_len t_limbs -> BS.bn_mod_slow_safe_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n"]
val mod_exp_vartime: len:BN.meta_len t_limbs -> BS.bn_mod_exp_safe_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n"]
val mod_exp_consttime: len:BN.meta_len t_limbs -> BS.bn_mod_exp_safe_st t_limbs len

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated,
  true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n"]
val mod_inv_prime_vartime: len:BN.meta_len t_limbs -> BS.bn_mod_inv_prime_safe_st t_limbs len

[@@ CPrologue
"\n/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/\n";

Comment "Heap-allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum64_mont_ctx_free on the return value
  to avoid memory leaks."]
val mont_ctx_init: len:BN.meta_len t_limbs -> MA.bn_field_init_st t_limbs len

[@@ Comment "Deallocate the memory previously allocated by Hacl_Bignum64_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init."]
val mont_ctx_free: MA.bn_field_free_st t_limbs

[@@ Comment "Write `a mod n` in `res`.

  The argument a is meant to be `2*len` limbs in size, i.e. uint64_t[2*len].
  The outparam res is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init."]
val mod_precomp: len:Ghost.erased _ -> BS.bn_mod_slow_ctx_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n"]
val mod_exp_vartime_precomp: len:Ghost.erased _ -> BS.bn_mod_exp_ctx_st t_limbs len

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n"]
val mod_exp_consttime_precomp: len:Ghost.erased _ -> BS.bn_mod_exp_ctx_st t_limbs len

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n"]
val mod_inv_prime_vartime_precomp: len:Ghost.erased _ -> BS.bn_mod_inv_prime_ctx_st t_limbs len

[@@ CPrologue
"\n/********************/
/* Loads and stores */
/********************/\n";
Comment
"Load a bid-endian bignum from memory.

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks."]
val new_bn_from_bytes_be: BS.new_bn_from_bytes_be_st t_limbs

[@@ Comment "Load a little-endian bignum from memory.

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks."]
val new_bn_from_bytes_le: BS.new_bn_from_bytes_le_st t_limbs

[@@ Comment "Serialize a bignum into big-endian memory.

  The argument b points to a bignum of ⌈len / 8⌉ size.
  The outparam res points to `len` bytes of valid memory."]
val bn_to_bytes_be: len:_ -> Hacl.Bignum.Convert.bn_to_bytes_be_st t_limbs len

[@@ Comment "Serialize a bignum into little-endian memory.

  The argument b points to a bignum of ⌈len / 8⌉ size.
  The outparam res points to `len` bytes of valid memory."]
val bn_to_bytes_le: len:_ -> Hacl.Bignum.Convert.bn_to_bytes_le_st t_limbs len

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
Comment "Returns 2^64 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be `len` limbs in size, i.e. uint64_t[len]."]
val lt_mask: len:_ -> BN.bn_lt_mask_st t_limbs len

[@@ Comment "Returns 2^64 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be `len` limbs in size, i.e. uint64_t[len]."]
val eq_mask: len:_ -> BN.bn_eq_mask_st t_limbs len
