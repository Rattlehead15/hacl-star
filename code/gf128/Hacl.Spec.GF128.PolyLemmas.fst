module Hacl.Spec.GF128.PolyLemmas

open Lib.IntTypes
open Lib.IntVector

open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2.Bits
open Vale.Math.Poly2.Lemmas

let lemma_of_to_uint_128 a =
  reveal_defs ();
  lemma_reverse_define_all ();
  lemma_equal a (of_uint 128 (to_uint 128 a))

let lemma_to_of_vec128 q =
  lemma_create_index_vec_w1 q

let lemma_of_to_vec128 a =
  ()

let lemma_vec128_zero () =
  lemma_bitwise_all ();
  Vale.Arch.TypesNative.lemma_zero_nth 128;
  lemma_equal zero (of_uint 128 0);
  ()

let lemma_vec128_ones () =
  lemma_bitwise_all ();
  lemma_equal (ones 128) (of_uint 128 0xffffffffffffffffffffffffffffffff);
  ()

let lemma_add128 a b =
  lemma_bitwise_all ();
  logxor_spec (mk_int #U128 #SEC (to_uint 128 a)) (mk_int #U128 #SEC (to_uint 128 b));
  assert (of_vec128 (to_vec128 a ^| to_vec128 b) ==
      of_uint 128 (FStar.UInt.logxor (to_uint 128 a) (to_uint 128 b))); //OBSERVE
  lemma_equal (a +. b) (of_vec128 (to_vec128 a ^| to_vec128 b));
  ()

let lemma_add_vec128 a b =
  lemma_add128 (of_vec128 a) (of_vec128 b);
  ()

let lemma_and128 a b =
  lemma_bitwise_all ();
  logand_spec (mk_int #U128 #SEC (to_uint 128 a)) (mk_int #U128 #SEC (to_uint 128 b));
  assert (of_vec128 (to_vec128 a &| to_vec128 b) ==
      of_uint 128 (FStar.UInt.logand (to_uint 128 a) (to_uint 128 b))); //OBSERVE
  lemma_equal (poly_and a b) (of_vec128 (to_vec128 a &| to_vec128 b));
  ()

let lemma_and_vec128 a b =
  lemma_and128 (of_vec128 a) (of_vec128 b);
  ()
