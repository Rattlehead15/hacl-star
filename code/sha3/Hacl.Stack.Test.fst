module Hacl.Stack.Test

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

inline_for_extraction noextract
val alloc_multi: _:unit ->
  Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

let alloc_multi _ =
  push_frame ();
  let h0 = ST.get() in
  let b0 = create 256ul (u8 0) in
  let b1 = create 256ul (u8 0) in
  let h1 = ST.get() in
  assert (stack_allocated b0 h0 h1 (Seq.create 256 (u8 0)));
  assert (stack_allocated b1 h0 h1 (Seq.create 256 (u8 0)));
  pop_frame()
