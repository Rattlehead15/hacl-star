module Hacl.Spec.GF128.Lemmas

open FStar.Mul
open Lib.LoopCombinators

open FStar.Tactics.V2
open FStar.Algebra.CommMonoid
open FStar.Tactics.CanonCommSemiring
open FStar.Math.Lemmas

open Vale.Math.Poly2
open Vale.Math.Poly2.Lemmas
open Vale.Math.Poly2.Galois

friend Lib.IntTypes

let poly_extensionality (a:elem) (b:elem) : Lemma
  (requires to_poly a == to_poly b)
  (ensures a == b)
  =
  lemma_felem_poly a;
  lemma_felem_poly b

let add_identity a =
  calc (==) {
    to_poly (zero +% a);
    (==) {lemma_add S.gf128 zero a}
    (to_poly (zero #S.gf128)) +. (to_poly a);
    (==)
    {
      lemma_zero S.gf128;
      lemma_add_zero (to_poly a);
      lemma_add_commute (to_poly a) (to_poly (zero #S.gf128))
    }
    to_poly a;
  };
  poly_extensionality (zero +% a) a

let mul_identity a =
  calc (==) {
    to_poly (one_be *% a);
    (==) {lemma_mul S.gf128 one_be a}
    (to_poly ((one_be #S.gf128)) *. (to_poly a) %. (irred_poly S.gf128));
    (==)
    {
      lemma_one S.gf128;
      lemma_mul_one (to_poly a);
      lemma_mul_commute (to_poly a) (to_poly (one_be #S.gf128))
    }
    (to_poly a %. (irred_poly S.gf128));
    (==) { lemma_mod_small (to_poly a) (irred_poly S.gf128) }
    to_poly a;
  };
  poly_extensionality (one_be *% a) a

let add_associativity a b c =
  calc (==) {
    to_poly (a +% (b +% c));
    (==) { lemma_add S.gf128 a (b +% c) }
    to_poly a +. to_poly (b +% c);
    (==) { lemma_add S.gf128 b c }
    to_poly a +. (to_poly b +. to_poly c);
    (==) { lemma_add_associate (to_poly a) (to_poly b) (to_poly c) }
    to_poly (a +% b +% c);
  };
  poly_extensionality (a +% (b +% c)) ((a +% b) +% c)

let add_commutativity a b =
  calc (==) {
    to_poly (a +% b);
    (==) { lemma_add S.gf128 a b }
    to_poly a +. to_poly b;
    (==) { lemma_add_commute (to_poly a) (to_poly b) }
    to_poly b +. to_poly a;
    (==) { lemma_add S.gf128 b a }
    to_poly (b +% a);
  };
  poly_extensionality (a +% b) (b +% a)

let mul_associativity a b c =
  calc (==) {
    to_poly (a *% (b *% c));
    (==) { lemma_mul S.gf128 a (b *% c) }
    to_poly a *. to_poly (b *% c) %. irred_poly S.gf128;
    (==) { lemma_mul S.gf128 b c }
    to_poly a *. (to_poly b *. to_poly c %. irred_poly S.gf128) %. irred_poly S.gf128;
    (==) { lemma_mod_mul_mod_right (to_poly a) (to_poly b *. to_poly c) (irred_poly S.gf128) }
    (to_poly a *. (to_poly b *. to_poly c)) %. irred_poly S.gf128;
    (==) { lemma_mul_associate (to_poly a) (to_poly b) (to_poly c) }
    (to_poly a *. to_poly b *. to_poly c) %. irred_poly S.gf128;
    (==) { lemma_mod_mul_mod (to_poly a *. to_poly b) (irred_poly S.gf128) (to_poly c) }
    ((to_poly a *. to_poly b) %. irred_poly S.gf128) *. to_poly c %. irred_poly S.gf128;
    (==) { lemma_mul S.gf128 a b }
    to_poly (a *% b) *. (to_poly c) %. irred_poly S.gf128;
    (==) { lemma_mul S.gf128 (a *% b) c }
    to_poly ((a *% b) *% c);
  };
  poly_extensionality (a *% b *% c) (a *% (b *% c))

let mul_commutativity a b =
  calc (==) {
    to_poly (a *% b);
    (==) { lemma_mul S.gf128 a b }
    to_poly a *. to_poly b %. irred_poly S.gf128;
    (==) { lemma_mul_commute (to_poly a) (to_poly b) }
    to_poly b *. to_poly a %. irred_poly S.gf128;
    (==) { lemma_mul S.gf128 b a }
    to_poly (b *% a);
  };
  poly_extensionality (a *% b) (b *% a)

[@canon_attr]
let elem_add_cm : cm elem =
  CM zero ( +% ) add_identity add_associativity add_commutativity

[@canon_attr]
let elem_mul_cm : cm elem =
  CM one_be ( *% ) mul_identity mul_associativity mul_commutativity

val add_opp: add_opp_r_lemma elem elem_add_cm id
let add_opp a =
  calc (==) {
    to_poly (a +% a);
    (==) { lemma_add S.gf128 a (a) }
    to_poly a +. to_poly (a);
    (==) { lemma_add_all () }
    Vale.Math.Poly2_s.zero;
  };
  poly_extensionality (a +% a) zero

val mul_add_distr: distribute_left_lemma elem elem_add_cm elem_mul_cm
let mul_add_distr a b c =
  calc (==) {
    to_poly (a *% (b +% c));
    (==) { lemma_mul S.gf128 a (b +% c) }
    to_poly a *. to_poly (b +% c) %. irred_poly S.gf128;
    (==) { lemma_add S.gf128 b c }
    to_poly a *. (to_poly b +. to_poly c) %. irred_poly S.gf128;
    (==) { lemma_mul_distribute_right (to_poly a) (to_poly b) (to_poly c) }
    (to_poly a *. to_poly b +. to_poly a *. to_poly c) %. irred_poly S.gf128;
    (==) { lemma_mod_distribute (to_poly a *. to_poly b) (to_poly a *. to_poly c) (irred_poly S.gf128) }
    to_poly a *. to_poly b %. irred_poly S.gf128 +. to_poly a *. to_poly c %. irred_poly S.gf128;
    (==) { lemma_mul S.gf128 a b }
    to_poly (a *% b) +. to_poly a *. to_poly c %. irred_poly S.gf128;
    (==) { lemma_mul S.gf128 a c }
    to_poly (a *% b) +. to_poly (a *% c);
    (==) { lemma_add S.gf128 (a *% b) (a *% c) }
    to_poly ((a *% b) +% (a *% c));
  };
  poly_extensionality (a *% (b +% c)) ((a *% b) +% (a *% c))

val mul_zero_l: mult_zero_l_lemma elem elem_add_cm elem_mul_cm
let mul_zero_l a =
  calc (==) {
    to_poly (zero *% a);
    (==) { lemma_mul S.gf128 zero a }
    to_poly (zero #S.gf128) *. to_poly a %. irred_poly S.gf128;
    (==) { lemma_zero S.gf128 }
    Vale.Math.Poly2_s.zero *. to_poly a %. irred_poly S.gf128;
    (==) { lemma_mul_all () }
    to_poly (zero #S.gf128) %. irred_poly S.gf128;
    (==) { lemma_mod_small (to_poly (zero #S.gf128)) (irred_poly S.gf128) }
    to_poly (zero #S.gf128);
  };
  poly_extensionality (zero *% a) zero

[@canon_attr]
let elem_cr : cr elem = CR elem_add_cm elem_mul_cm id add_opp mul_add_distr mul_zero_l

let gf128_semiring () : Tac unit = canon_semiring elem_cr


let gf128_update_multi_mul_add_lemma_load_acc_aux a0 b0 b1 b2 b3 r =
  admit();
  add_identity b1;
  add_identity b2;
  add_identity b3;
  assert (
    (a0 +% b0) *% (r *% (r *% (r *% r))) +% b1 *% (r *% (r *% r)) +% b2 *% (r *% r) +% b3 *% r ==
    ((((a0 +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)
  by (gf128_semiring ())

let gf128_update_multi_mul_add_lemma_loop_aux a0 a1 a2 a3 b0 b1 b2 b3 r =
  admit();
  assert (
    (a0 *% (r *% (r *% (r *% r))) +% b0) *% (r *% (r *% (r *% r))) +%
    (a1 *% (r *% (r *% (r *% r))) +% b1) *% (r *% (r *% r)) +%
    (a2 *% (r *% (r *% (r *% r))) +% b2) *% (r *% r) +%
    (a3 *% (r *% (r *% (r *% r))) +% b3) *% r ==
    ((((a0 *% (r *% (r *% (r *% r))) +%
        a1 *% (r *% (r *% r)) +%
	a2 *% (r *% r) +%
	a3 *% r +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)
  by (gf128_semiring ())


module BV = FStar.BitVector

let to_vec128 (x:uint128) : BV.bv_t 128 = UInt.to_vec #128 (v x)
let to_vec64 (x:uint64) : BV.bv_t 64 = UInt.to_vec #64 (v x)

val to_vec128_lemma : x:elem_s -> Lemma
  (to_vec128 (to_elem x) == Seq.append (to_vec64 x.[1]) (to_vec64 x.[0]))
let to_vec128_lemma x =
  UInt.append_lemma (to_vec64 x.[1]) (to_vec64 x.[0])

val logxor_vec_lemma: x:elem_s -> y:elem_s -> Lemma
  (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)) ==
   Seq.append (BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0])))
let logxor_vec_lemma x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  Seq.lemma_eq_intro
    (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)))
    (Seq.append (BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0])))

let logxor_s_lemma x y =
  assert (to_vec128 (to_elem x ^. to_elem y) == BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)));
  logxor_vec_lemma x y;
  assert (to_vec128 (to_elem x ^. to_elem y) == Seq.append (BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0])));
  let lp = logxor_s x y in
  assert (to_vec64 lp.[0] == BV.logxor_vec (to_vec64 x.[0]) (to_vec64 y.[0]));
  assert (to_vec64 lp.[1] == BV.logxor_vec (to_vec64 x.[1]) (to_vec64 y.[1]));
  to_vec128_lemma lp

val logand_vec_lemma: x:elem_s -> y:elem_s -> Lemma
  (BV.logand_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)) ==
   Seq.append (BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0])))
let logand_vec_lemma x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  Seq.lemma_eq_intro
    (BV.logand_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)))
    (Seq.append (BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0])))

let logand_s_lemma x y =
  assert (to_vec128 (to_elem x &. to_elem y) == BV.logand_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)));
  logand_vec_lemma x y;
  assert (to_vec128 (to_elem x &. to_elem y) == Seq.append (BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1])) (BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0])));
  let lp = logand_s x y in
  assert (to_vec64 lp.[0] == BV.logand_vec (to_vec64 x.[0]) (to_vec64 y.[0]));
  assert (to_vec64 lp.[1] == BV.logand_vec (to_vec64 x.[1]) (to_vec64 y.[1]));
  to_vec128_lemma lp
