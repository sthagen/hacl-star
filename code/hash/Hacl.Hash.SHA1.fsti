module Hacl.Hash.SHA1

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

include Hacl.Hash.Core.SHA1

val legacy_update_multi: update_multi_st (|SHA1, ()|)
val legacy_update_last: update_last_st (|SHA1, ()|)
val legacy_hash: hash_st SHA1
