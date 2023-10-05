module Hacl.Spec.GF128.PolyLemmas_helpers

open FStar.Mul

open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2.Lemmas
open Vale.AES.GF128_s

// of_fun 8 (fun (i:nat) -> i = 0 || i = 1 || i = 2 || i = 7)
let gf128_low : poly = gf128_modulus_low_terms

// of_fun 8 (fun (i:nat) -> i = 0 || i = 1 || i = 6)
let gf128_low_shift : poly = shift gf128_modulus_low_terms (-1)

val lemma_mul_h_shift_right (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures a *. h == shift a 63 +. shift a 62 +. shift a 57)

val lemma_mul_h_shift_right_mod (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures (a *. h) %. monomial 64 ==
    shift a 63 %. monomial 64 +. shift a 62 %. monomial 64 +. shift a 57 %. monomial 64)

val lemma_mul_h_shift_left (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures (a *. h) /. monomial 64 == shift a (-1) +. shift a (-2) +. shift a (-7))

val lemma_mul_h (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures a *. h == (shift a (-1) +. shift a (-2) +. shift a (-7)) *. monomial 64 +.
    (shift a 63 +. shift a 62 +. shift a 57) %. monomial 64)

val lemma_mul_h_2_zero (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures (((a *. h) %. monomial 64) *. h) %. monomial 64 == zero)

val lemma_shift_left_cancel (a a0 a1:poly) : Lemma
  (requires degree a <= 127 /\ degree a0 <= 63 /\
    degree a1 <= 63 /\ a == (shift a1 64) +. a0)
  (ensures shift (a %. monomial 64) 64 == shift a0 64)

val lemma_shift_right_cancel (a a0 a1:poly) : Lemma
  (requires degree a <= 127 /\ degree a0 <= 63 /\
    degree a1 <= 63 /\ a == (shift a1 64) +. a0)
  (ensures shift a (-64) == a1)

val lemma_add_left_shift (a0 a1 b:poly) : Lemma
  (requires degree a0 <= 63 /\ degree a1 <= 63 /\ degree b <= 63)
  (ensures (shift a1 64) +. a0 +. (shift b 64) == (shift (a1 +. b) 64) +. a0)

val lemma_add_left_shift_double (a0 a1 b0 b1:poly) : Lemma
  (requires degree a0 <= 63 /\ degree a1 <= 63 /\
    degree b0 <= 63 /\ degree b1 <= 63)
  (ensures (shift a1 64) +. a0 +. (shift b1 64 +. b0) ==
    (shift (a1 +. b1) 64) +. (a0 +. b0))

val lemma_mul_x (hi lo:poly) : Lemma
  (requires degree hi <= 126 /\ degree lo <= 127)
  (ensures (
    let n = monomial 64 in
    let nn = monomial 128 in
    let l0_r63 = shift (lo %. n) (-63) in
    let l1_r63 = shift (lo /. n) (-63) in
    let l0_l1 = (shift (lo %. n) 1) %. n in
    let l1_l1 = (shift (lo /. n) 1) %. n in
    let h0_r63 = shift (hi %. n) (-63) in
    let h0_l1 = (shift (hi %. n) 1) %. n in
    let h1_l1 = (shift (hi /. n) 1) %. n in
    shift (hi *. nn +. lo) 1 == 
      (shift (h1_l1 +. h0_r63) 64 +. (h0_l1 +. l1_r63)) *. nn +.
        (shift (l1_l1 +. l0_r63) 64 +. l0_l1)
  ))

val lemma_reduce_helper (a h:poly) : Lemma
  (requires degree a <= 127 /\ h == reverse gf128_low_shift 63)
  (ensures (
    let n = monomial 64 in
    let y_10c = swap a 64 +. (mask a 64) *. h in
    swap y_10c 64 +. mask y_10c 64 *. h == 
      (shift ((a /. n +. ((a %. n) *. h) %. n) +. 
        (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)) 64 +.
          (a %. n +. (((a %. n) *. h) /. n +. ((a /. n) *. h) %. n)))
  ))

val lemma_reduce_rev_helper (a0 a1 h:poly) (n:pos) : Lemma
  (requires
    n == 64 /\
    degree a0 < n + n /\
    degree a1 < n + n /\
    degree (monomial (n + n) +. h) == n + n /\
    degree h < n /\
    h.[0]
  )
  (ensures (
    let nn = n + n in
    let mm = monomial nn in
    let m = monomial n in
    let g = mm +. h in
    let c = reverse (shift h (-1)) (n - 1) in
    let y_10c = swap a0 64 +. (mask a0 64) *. c in
    let a = a0 +. shift a1 128 in
    let x = reverse a (nn + nn - 1) in
    reverse (x %. g) (nn - 1) == swap y_10c 64 +. mask y_10c 64 *. c +. a1
  ))
