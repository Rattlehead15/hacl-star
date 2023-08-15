module EverCrypt.Hash.Incremental

open FStar.Mul

// Watch out: keep the module declarations in sync between fsti and fst
// (otherwise interleaving issues may bite).
module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module G = FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor

module Hash = EverCrypt.Hash

open FStar.HyperStack.ST
open Spec.Hash.Definitions
open Hacl.Streaming.Interface

include Spec.Hash.Definitions
include Hacl.Hash.Definitions

open Spec.Hash.Lemmas

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

private
val hash_256: Hacl.Hash.Definitions.hash_st SHA2_256

// A full one-shot hash that relies on vale at each multiplexing point
let hash_256 input input_len dst = ()
