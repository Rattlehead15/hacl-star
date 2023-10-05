module Hacl.Spec.GF128.PolyLemmas_helpers

open FStar.Mul

open Vale.Math.Poly2.Bits

let lemma_mul_h_shift_right a h =
  lemma_bitwise_all ();
  calc (==) {
    a *. h;
    == {lemma_equal h (monomial 63 +. monomial 62 +. monomial 57)}
    a *. (monomial 63 +. monomial 62 +. monomial 57);
    == {lemma_mul_distribute_right a (monomial 63 +. monomial 62) (monomial 57)}
    (a *. (monomial 63 +. monomial 62)) +. (a *. monomial 57);
    == {lemma_mul_distribute_right a (monomial 63) (monomial 62)}
    (a *. monomial 63) +. (a *. monomial 62) +. (a *. monomial 57);
    == {
      lemma_shift_is_mul a 63;
      lemma_shift_is_mul a 62;
      lemma_shift_is_mul a 57
    }
    (shift a 63) +. (shift a 62) +. (shift a 57);
  }

let lemma_mul_h_shift_right_mod a h =
  calc (==) {
    (a *. h) %. monomial 64;
    == {lemma_mul_h_shift_right a h}
    (shift a 63 +. shift a 62 +. shift a 57) %. monomial 64;
    == {lemma_mod_distribute (shift a 63 +. shift a 62) (shift a 57) (monomial 64)}
    (shift a 63 +. shift a 62) %. monomial 64 +. shift a 57 %. monomial 64;
    == {lemma_mod_distribute (shift a 63) (shift a 62) (monomial 64)}
    shift a 63 %. monomial 64 +. shift a 62 %. monomial 64 +. shift a 57 %. monomial 64;
  }

let lemma_mul_h_shift_left a h =
  lemma_bitwise_all ();
  lemma_shift_is_div (a *. h) 64;
  lemma_mul_h_shift_right a h;
  lemma_equal (shift (shift a 63 +. shift a 62 +. shift a 57) (-64))
    (shift (shift a 63) (-64) +. shift (shift a 62) (-64) +. shift (shift a 57) (-64));
  lemma_shift_shift a 63 (-64);
  lemma_shift_shift a 62 (-64);
  lemma_shift_shift a 57 (-64)

let lemma_mul_h a h =
  lemma_div_mod (a *. h) (monomial 64);
  lemma_mul_h_shift_right a h;
  lemma_mul_h_shift_left a h

val lemma_h_2 (h:poly) : Lemma
  (requires h == reverse gf128_low_shift 63)
  (ensures h *. h == monomial 126 +. monomial 124 +. monomial 114)

let lemma_h_2 h =
  lemma_bitwise_all ();
  calc (==) {
    h *. h;
    == {lemma_equal h (monomial 63 +. monomial 62 +. monomial 57)}
    (monomial 63 +. monomial 62 +. monomial 57) *. h;
    == {lemma_mul_distribute_left (monomial 63 +. monomial 62) (monomial 57) h}
    (monomial 63 +. monomial 62) *. h +. (monomial 57) *. h;
    == {lemma_mul_distribute_left (monomial 63) (monomial 62) h}
    (monomial 63) *. h +. (monomial 62) *. h +. (monomial 57) *. h;
    == {lemma_equal h (monomial 63 +. monomial 62 +. monomial 57)}
    (monomial 63) *. (monomial 63 +. monomial 62 +. monomial 57) +.
      (monomial 62) *. (monomial 63 +. monomial 62 +. monomial 57) +.
      (monomial 57) *. (monomial 63 +. monomial 62 +. monomial 57);
    == {
      lemma_mul_distribute_right (monomial 63) (monomial 63 +. monomial 62) (monomial 57);
      lemma_mul_distribute_right (monomial 62) (monomial 63 +. monomial 62) (monomial 57);
      lemma_mul_distribute_right (monomial 57) (monomial 63 +. monomial 62) (monomial 57)
    }
    (monomial 63 *. (monomial 63 +. monomial 62) +. monomial 63 *. monomial 57) +.
      (monomial 62 *. (monomial 63 +. monomial 62) +. monomial 62 *. monomial 57) +.
      (monomial 57 *. (monomial 63 +. monomial 62) +. monomial 57 *. monomial 57);
    == {
      lemma_mul_distribute_right (monomial 63) (monomial 63) (monomial 62);
      lemma_mul_distribute_right (monomial 62) (monomial 63) (monomial 62);
      lemma_mul_distribute_right (monomial 57) (monomial 63) (monomial 62)
    }
    (monomial 63 *. monomial 63 +. monomial 63 *. monomial 62 +. monomial 63 *. monomial 57) +.
      (monomial 62 *. monomial 63 +. monomial 62 *. monomial 62 +. monomial 62 *. monomial 57) +.
      (monomial 57 *. monomial 63 +. monomial 57 *. monomial 62 +. monomial 57 *. monomial 57);
    == {
      lemma_mul_monomials 63 63; lemma_mul_monomials 63 62; lemma_mul_monomials 63 57;
      lemma_mul_monomials 62 63; lemma_mul_monomials 62 62; lemma_mul_monomials 62 57;
      lemma_mul_monomials 57 63; lemma_mul_monomials 57 62; lemma_mul_monomials 57 57
    }
    (monomial 126 +. monomial 125 +. monomial 120) +.
      (monomial 125 +. monomial 124 +. monomial 119) +.
      (monomial 120 +. monomial 119 +. monomial 114);
    == {
      lemma_equal ((monomial 126 +. monomial 125 +. monomial 120) +.
        (monomial 125 +. monomial 124 +. monomial 119) +.
        (monomial 120 +. monomial 119 +. monomial 114)) (monomial 126 +. monomial 124 +. monomial 114)
    }
    monomial 126 +. monomial 124 +. monomial 114;
  }

let lemma_mul_h_2_zero a h =
  reveal_defs ();
  calc (==) {
    (((a *. h) %. monomial 64) *. h) %. monomial 64;
    == {lemma_mod_mul_mod (a *. h) (monomial 64) h}
    ((a *. h) *. h) %. monomial 64;
    == {lemma_mul_associate a h h}
    (a *. (h *. h)) %. monomial 64;
    == {lemma_mod_mul_mod_right a (h *. h) (monomial 64)}
    (a *. ((h *. h) %. monomial 64)) %. monomial 64;
    == {lemma_h_2 h}
    (a *. ((monomial 126 +. monomial 124 +. monomial 114) %. monomial 64)) %. monomial 64;
    == {lemma_mod_distribute (monomial 126 +. monomial 124) (monomial 114) (monomial 64)}
    (a *. ((monomial 126 +. monomial 124) %. monomial 64 +. monomial 114 %. monomial 64)) %. monomial 64;
    == {lemma_mod_distribute (monomial 126) (monomial 124) (monomial 64)}
    (a *. (monomial 126 %. monomial 64 +. monomial 124 %. monomial 64 +. monomial 114 %. monomial 64)) %. monomial 64;
    == {
      lemma_mul_monomials 62 64;
      lemma_add_zero (monomial 126);
      lemma_div_mod_unique ((monomial 126) +. zero) (monomial 64) (monomial 62) zero;
      // --> monomial 126 %. monomial 64 == zero
      lemma_mul_monomials 60 64;
      lemma_add_zero (monomial 124);
      lemma_div_mod_unique ((monomial 124) +. zero) (monomial 64) (monomial 60) zero;
      // --> monomial 126 %. monomial 64 == zero
      lemma_mul_monomials 50 64;
      lemma_add_zero (monomial 114);
      lemma_div_mod_unique ((monomial 114) +. zero) (monomial 64) (monomial 50) zero
      // --> monomial 126 %. monomial 64 == zero
    }
    (a *. (zero +. zero +. zero)) %. monomial 64;
    == {lemma_add_zero zero}
    (a *. zero) %. monomial 64;
    == {lemma_mul_zero a}
    zero;
  }

let lemma_shift_left_cancel a a0 a1 =
  reveal_defs ();
  calc (==) {
    shift (((shift a1 64) +. a0) %. monomial 64) 64;
    == {lemma_shift_is_mul a1 64}
    shift ((a1 *. monomial 64 +. a0) %. monomial 64) 64;
    == {lemma_mod_distribute (a1 *. monomial 64) a0 (monomial 64)}
    shift ((a1 *. monomial 64) %. monomial 64 +. a0 %. monomial 64) 64;
    == {lemma_mod_small a0 (monomial 64)}
    shift ((a1 *. monomial 64) %. monomial 64 +. a0) 64;
    == {lemma_mod_mul_mod_right a1 (monomial 64) (monomial 64)}
    shift ((a1 *. (mod (monomial 64) (monomial 64))) %. monomial 64 +. a0) 64;
    == {lemma_mod_cancel (monomial 64)}
    shift ((a1 *. zero) %. monomial 64 +. a0) 64;
    == {lemma_mul_zero a1; lemma_add_zero_left a0}
    shift a0 64;
  }

let lemma_shift_right_cancel a a0 a1 =
  lemma_shift_is_div a 64;
  lemma_shift_is_mul a1 64;
  lemma_div_mod_unique a (monomial 64) a1 a0

let lemma_add_left_shift a0 a1 b =
  lemma_bitwise_all ();
  calc (==) {
    (shift a1 64) +. a0 +. (shift b 64);
    == {lemma_add_commute (shift a1 64) a0}
    a0 +. (shift a1 64) +. (shift b 64);
    == {lemma_add_associate a0 (shift a1 64) (shift b 64)}
    a0 +. ((shift a1 64) +. (shift b 64));
    == {lemma_shift_is_mul a1 64; lemma_shift_is_mul b 64}
    a0 +. (a1 *. monomial 64 +. b *. monomial 64);
    == {lemma_mul_distribute_left a1 b (monomial 64)}
    a0 +. (a1 +. b) *. monomial 64;
    == {lemma_shift_is_mul (a1 +. b) 64}
    a0 +. (shift (a1 +. b) 64);
    == {lemma_add_commute a0 (shift (a1 +. b) 64)}
    (shift (a1 +. b) 64) +. a0;
  }

let lemma_add_left_shift_double a0 a1 b0 b1 =
  lemma_bitwise_all ();
  calc (==) {
    (shift a1 64) +. a0 +. (shift b1 64 +. b0);
    == {lemma_add_associate ((shift a1 64) +. a0) (shift b1 64) b0}
    ((shift a1 64) +. a0 +. shift b1 64) +. b0;
    == {lemma_add_commute (shift a1 64) a0}
    (a0 +. (shift a1 64) +. shift b1 64) +. b0;
    == {lemma_add_associate a0 (shift a1 64) (shift b1 64)}
    (a0 +. (shift a1 64 +. shift b1 64)) +. b0;
    == {lemma_shift_is_mul a1 64; lemma_shift_is_mul b1 64}
    (a0 +. (a1 *. monomial 64 +. b1 *. monomial 64)) +. b0;
    == {lemma_mul_distribute_left a1 b1 (monomial 64)}
    (a0 +. (a1 +. b1) *. monomial 64) +. b0;
    == {lemma_shift_is_mul (a1 +. b1) 64}
    (a0 +. (shift (a1 +. b1) 64)) +. b0;
    == {lemma_add_commute a0 (shift (a1 +. b1) 64)}
    ((shift (a1 +. b1) 64) +. a0) +. b0;
    == {lemma_add_associate (shift (a1 +. b1) 64) a0 b0}
    (shift (a1 +. b1) 64) +. (a0 +. b0);
  }

val lemma_mul_128_x (a:poly) : Lemma
  (requires degree a <= 127 )
  (ensures (
    let n = monomial 64 in
    let nn = monomial 128 in
    let l0_r63 = shift (a %. n) (-63) in
    let l1_r63 = shift (a /. n) (-63) in
    let l0_l1 = (shift (a %. n) 1) %. n in
    let l1_l1 = (shift (a /. n) 1) %. n in
    a *. monomial 1 == l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1
  ))

let lemma_mul_128_x a =
  let n = monomial 64 in
  let nn = monomial 128 in
  let l0_r63 = shift (a %. n) (-63) in
  let l1_r63 = shift (a /. n) (-63) in
  let l0_l1 = (shift (a %. n) 1) %. n in
  let l1_l1 = (shift (a /. n) 1) %. n in
  calc (==) {
    a *. monomial 1;
    == {lemma_div_mod a n}
    ((a /. n) *. n +. (a %. n)) *. monomial 1;
    == {lemma_mul_distribute_left ((a /. n) *. n) (a %. n) (monomial 1)}
    ((a /. n) *. n) *. monomial 1 +. (a %. n) *. monomial 1;
    == {lemma_shift_is_mul (a %. n) 1}
    ((a /. n) *. n) *. monomial 1 +. (shift (a %. n) 1);
    == {lemma_div_mod (shift (a %. n) 1) n}
    ((a /. n) *. n) *. monomial 1 +.
      (((shift (a %. n) 1) /. n) *. n +. ((shift (a %. n) 1) %. n));
    == {lemma_shift_is_div (shift (a %. n) 1) 64}
    ((a /. n) *. n) *. monomial 1 +.
      ((shift (shift (a %. n) 1) (-64)) *. n +. ((shift (a %. n) 1) %. n));
    == {lemma_shift_shift (a %. n) 1 (-64)}
    ((a /. n) *. n) *. monomial 1 +. (l0_r63 *. n +. l0_l1);
    == {
      lemma_mul_commute (a /. n) n;
      lemma_mul_associate n (a /. n) (monomial 1);
      lemma_mul_commute n ((a /. n) *. monomial 1)
    }
    ((a /. n) *. monomial 1) *. n +. (l0_r63 *. n +. l0_l1);
    == {lemma_shift_is_mul (a /. n) 1}
    (shift (a /. n) 1) *. n +. (l0_r63 *. n +. l0_l1);
    == {lemma_div_mod (shift (a /. n) 1) n}
    (((shift (a /. n) 1) /. n) *. n +. ((shift (a /. n) 1) %. n)) *. n +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_mul_distribute_left (((shift (a /. n) 1) /. n) *. n) ((shift (a /. n) 1) %. n) n}
    (((shift (a /. n) 1) /. n) *. n *. n +. ((shift (a /. n) 1) %. n) *. n) +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_shift_is_div (shift (a /. n) 1) 64}
    ((shift (shift (a /. n) 1) (-64)) *. n *. n +. ((shift (a /. n) 1) %. n) *. n) +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_shift_shift (a /. n) 1 (-64)}
    ((shift (a /. n) (-63)) *. n *. n +. ((shift (a /. n) 1) %. n) *. n) +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_mul_associate (shift (a /. n) (-63)) n n; lemma_mul_monomials 64 64}
    l1_r63 *. nn +. l1_l1 *. n +. (l0_r63 *. n +. l0_l1);
    == {lemma_add_associate (l1_r63 *. nn +. l1_l1 *. n) (l0_r63 *. n) l0_l1}
    (l1_r63 *. nn +. l1_l1 *. n +. l0_r63 *. n) +. l0_l1;
    == {lemma_add_associate (l1_r63 *. nn) (l1_l1 *. n) (l0_r63 *. n)}
    l1_r63 *. nn +. (l1_l1 *. n +. l0_r63 *. n) +. l0_l1;
    == {lemma_mul_distribute_left l1_l1 l0_r63 n}
    l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1;
  }

let lemma_mul_x hi lo =
  let n = monomial 64 in
  let nn = monomial 128 in
  let l0_r63 = shift (lo %. n) (-63) in
  let l1_r63 = shift (lo /. n) (-63) in
  let l0_l1 = (shift (lo %. n) 1) %. n in
  let l1_l1 = (shift (lo /. n) 1) %. n in
  let h0_r63 = shift (hi %. n) (-63) in
  let h1_r63 = shift (hi /. n) (-63) in
  let h0_l1 = (shift (hi %. n) 1) %. n in
  let h1_l1 = (shift (hi /. n) 1) %. n in
  calc (==) {
    shift (hi *. nn +. lo) 1;
    == {lemma_shift_is_mul (hi *. nn +. lo) 1}
    (hi *. nn +. lo) *. monomial 1;
    == {lemma_mul_distribute_left (hi *. nn) lo (monomial 1)}
    hi *. nn *. monomial 1 +. lo *. monomial 1;
    == {
      lemma_mul_commute hi nn;
      lemma_mul_associate nn hi (monomial 1);
      lemma_mul_commute nn (hi *. monomial 1)
    }
    hi *. monomial 1 *. nn +. lo *. monomial 1;
    == {lemma_mul_128_x hi; lemma_mul_128_x lo}
    (h1_r63 *. nn +. (h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1);
    == {
      lemma_shift_is_div hi 64;
      lemma_shift_shift hi (-64) (-63);
      lemma_shift_degree hi (-127);
      lemma_degree_negative h1_r63
    }
    (zero *. nn +. (h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1);
    == {
      lemma_mul_commute zero nn;
      lemma_mul_zero nn;
      lemma_add_zero_left ((h1_l1 +. h0_r63) *. n)
    }
    ((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1);
    == {lemma_add_associate (l1_r63 *. nn) ((l1_l1 +. l0_r63) *. n) l0_l1}
    ((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. ((l1_l1 +. l0_r63) *. n +. l0_l1));
    == {
      lemma_add_associate (((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn) 
        (l1_r63 *. nn) ((l1_l1 +. l0_r63) *. n +. l0_l1)
    }
    (((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +. l1_r63 *. nn) +.
      ((l1_l1 +. l0_r63) *. n +. l0_l1);
    == {lemma_mul_distribute_left ((h1_l1 +. h0_r63) *. n +. h0_l1) l1_r63 nn}
    ((((h1_l1 +. h0_r63) *. n +. h0_l1) +. l1_r63) *. nn) +.
      ((l1_l1 +. l0_r63) *. n +. l0_l1);
    == {lemma_add_associate ((h1_l1 +. h0_r63) *. n) h0_l1 l1_r63}
    ((h1_l1 +. h0_r63) *. n +. (h0_l1 +. l1_r63)) *. nn +.
      ((l1_l1 +. l0_r63) *. n +. l0_l1);
    == {
      lemma_shift_is_mul (h1_l1 +. h0_r63) 64;
      lemma_shift_is_mul (l1_l1 +. l0_r63) 64
    }
    (shift (h1_l1 +. h0_r63) 64 +. (h0_l1 +. l1_r63)) *. nn +.
      (shift (l1_l1 +. l0_r63) 64 +. l0_l1);
  }

let lemma_reduce_helper a h =
  let n = monomial 64 in
  let y_10c = swap a 64 +. (mask a 64) *. h in
  calc (==) {
    swap a 64 +. (mask a 64) *. h;
    == {lemma_mask_is_mod a 64; lemma_shift_is_div a 64}
    (shift (a %. n) 64 +. a /. n) +. (a %. n) *. h;
    == {lemma_div_mod ((a %. n) *. h) n}
    (shift (a %. n) 64 +. a /. n) +.
      ((((a %. n) *. h) /. n) *. n +. ((a %. n) *. h) %. n);
    == {lemma_shift_is_mul (((a %. n) *. h) /. n) 64}
    (shift (a %. n) 64 +. a /. n) +.
      (shift (((a %. n) *. h) /. n) 64 +. ((a %. n) *. h) %. n);
    == {lemma_add_left_shift_double (a /. n) (a %. n) 
          (((a %. n) *. h) %. n) (((a %. n) *. h) /. n)}
    shift (a %. n +. ((a %. n) *. h) /. n) 64 +.
      (a /. n +. ((a %. n) *. h) %. n);
  };
  calc (==) {
    swap y_10c 64;
    == {lemma_mask_is_mod y_10c 64; lemma_shift_is_div y_10c 64}
    shift (y_10c %. n) 64 +. y_10c /. n;
    == {
      lemma_shift_is_mul (a %. n +. ((a %. n) *. h) /. n) 64;
      lemma_div_mod_unique y_10c n (a %. n +. ((a %. n) *. h) /. n)
          (a /. n +. ((a %. n) *. h) %. n)
    }
    shift (a /. n +. ((a %. n) *. h) %. n) 64 +.
      (a %. n +. ((a %. n) *. h) /. n);
  };
  calc (==) {
    mask y_10c 64 *. h;
    == {lemma_mask_is_mod y_10c 64}
    (y_10c %. n) *. h;
    == {
      lemma_shift_is_mul (a %. n +. ((a %. n) *. h) /. n) 64;
      lemma_div_mod_unique y_10c n (a %. n +. ((a %. n) *. h) /. n)
          (a /. n +. ((a %. n) *. h) %. n)
    }
    (a /. n +. ((a %. n) *. h) %. n) *. h;
    == {
      lemma_div_mod ((a /. n +. ((a %. n) *. h) %. n) *. h) n;
      lemma_shift_is_mul (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64
    }
    shift (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64 +.
        ((a /. n +. ((a %. n) *. h) %. n) *. h) %. n;
    == {
      lemma_mul_distribute_left (a /. n) (((a %. n) *. h) %. n) h;
      lemma_mod_distribute ((a /. n) *. h) ((((a %. n) *. h) %. n) *. h) n
    }
    shift (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64 +.
        (((a /. n) *. h) %. n +. ((((a %. n) *. h) %. n) *. h) %. n);
    == {
      lemma_mul_h_2_zero (a %. n) h;
      lemma_add_zero_right (((a /. n) *. h) %. n)
    }
    shift (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64 +.
        ((a /. n) *. h) %. n;
  };
  calc (==) {
    swap y_10c 64 +. mask y_10c 64 *. h;
    == {lemma_add_left_shift_double (a %. n +. ((a %. n) *. h) /. n) 
          (a /. n +. ((a %. n) *. h) %. n)
          (((a /. n) *. h) %. n)
          (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)}
    shift ((a /. n +. ((a %. n) *. h) %. n) +. 
      (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)) 64 +.
        ((a %. n +. ((a %. n) *. h) /. n) +. ((a /. n) *. h) %. n);
    == {lemma_add_associate (a %. n) (((a %. n) *. h) /. n)
          (((a /. n) *. h) %. n)}
    shift ((a /. n +. ((a %. n) *. h) %. n) +. 
      (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)) 64 +.
        (a %. n +. (((a %. n) *. h) /. n +. ((a /. n) *. h) %. n));
  }

open Vale.AES.GF128

let lemma_reduce_rev_helper a0 a1 h n =
  let c = reverse (shift h (-1)) (n - 1) in
  let y_10c = swap a0 64 +. (mask a0 64) *. c in
  reveal_defs ();
  lemma_mask_is_mod zero 64;
  lemma_add_zero_right a0;
  lemma_add_zero_right a1;
  lemma_add_commute (swap y_10c 64) a1;
  lemma_add_associate a1 (swap y_10c 64) (mask y_10c 64 *. c);
  lemma_add_commute a1 ((swap y_10c 64) +. (mask y_10c 64 *. c));
  lemma_reduce_rev a0 zero a1 h n;
  ()
