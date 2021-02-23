module Hacl.Streaming.Blake2s_128

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
open Hacl.Streaming.Blake2
module Blake2s128 = Hacl.Blake2s_128

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// The functor
inline_for_extraction noextract
let blake2s_128 (no_key : bool) (key_size : key_size_t Spec.Blake2S no_key) =
  blake2 Spec.Blake2S M128 Blake2s128.blake2s_init Blake2s128.blake2s_update_multi
         Blake2s128.blake2s_update_last Blake2s128.blake2s_finish no_key key_size 

/// Type abbreviations
let blake2s_128_block_state = s Spec.Blake2S M128
// The key parameters have no importance for the extracted state definitions
let blake2s_128_state = F.state_s (blake2s_128 true 0ul) () (s Spec.Blake2S M128) (optional_key_blake2s true 0ul)

/// No key
inline_for_extraction noextract
let blake2s_128_no_key_alloca =
  F.alloca (blake2s_128 true 0ul) () (s Spec.Blake2S M128)
           (optional_key_blake2s true 0ul)

[@ (Comment "  State allocation function when there is no key")]
let blake2s_128_no_key_create_in =
  F.create_in (blake2s_128 true 0ul) () (s Spec.Blake2S M128)
              (optional_key_blake2s true 0ul)

[@ (Comment "  (Re-)initialization function when there is no key")]
let blake2s_128_no_key_init =
  F.init (blake2s_128 true 0ul) () (s Spec.Blake2S M128)
              (optional_key_blake2s true 0ul)

[@ (Comment "  Update function when there is no key")]
let blake2s_128_no_key_update =
  F.update (blake2s_128 true 0ul) (G.hide ()) (s Spec.Blake2S M128)
           (optional_key_blake2s true 0ul)

[@ (Comment "  Finish function when there is no key")]
let blake2s_128_no_key_finish =
  F.mk_finish (blake2s_128 true 0ul) () (s Spec.Blake2S M128)
              (optional_key_blake2s true 0ul)

[@ (Comment "  Free state function when there is no key")]
let blake2s_128_no_key_free =
  F.free (blake2s_128 true 0ul) (G.hide ()) (s Spec.Blake2S M128)
         (optional_key_blake2s true 0ul)

/// With key
inline_for_extraction noextract
let blake2s_128_with_key_alloca (key_size : key_size_t Spec.Blake2S false) =
  F.alloca (blake2s_128 false key_size) () (s Spec.Blake2S M128)
           (optional_key_blake2s false key_size)

[@ (Comment "  State allocation function when using a (potentially null) key")]
let blake2s_128_with_key_create_in (key_size : key_size_t Spec.Blake2S false) =
  F.create_in (blake2s_128 false key_size) () (s Spec.Blake2S M128)
              (optional_key_blake2s false key_size)

[@ (Comment "  (Re-)initialization function when using a (potentially null) key")]
let blake2s_128_with_key_init (key_size : key_size_t Spec.Blake2S false) =
  F.init (blake2s_128 false key_size) () (s Spec.Blake2S M128)
              (optional_key_blake2s false key_size)

[@ (Comment "  Update function when using a (potentially null) key")]
let blake2s_128_with_key_update (key_size : key_size_t Spec.Blake2S false) =
  F.update (blake2s_128 false key_size) (G.hide ()) (s Spec.Blake2S M128)
           (optional_key_blake2s false key_size)

[@ (Comment "  Finish function when using a (potentially null) key")]
let blake2s_128_with_key_finish (key_size : key_size_t Spec.Blake2S false) =
  F.mk_finish (blake2s_128 false key_size) () (s Spec.Blake2S M128)
              (optional_key_blake2s false key_size)

[@ (Comment "  Free state function when using a (potentially null) key")]
let blake2s_128_with_key_free (key_size : key_size_t Spec.Blake2S false) =
  F.free (blake2s_128 false key_size) (G.hide ()) (s Spec.Blake2S M128)
         (optional_key_blake2s false key_size)
