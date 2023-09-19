module Hacl.Spec.Gf128.FieldNI

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Lemmas
open Vale.AES.GF128
open Vale.AES.GHash_BE

open Hacl.Spec.GF128.Poly_s
open Hacl.Spec.GF128.PolyLemmas

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let to_elem (s:vec128) : S.elem =
  index (vec_v s) 0

inline_for_extraction noextract
let to_elem4 (x1:vec128) (x2:vec128) (x3:vec128) (x4:vec128) : Vec.elem4 =
  create4 (index (vec_v x1) 0) (index (vec_v x2) 0) (index (vec_v x3) 0) (index (vec_v x4) 0)

inline_for_extraction
let cl_add (x:vec128) (y:vec128) : Tot vec128 = vec_xor x y

val lemma_cl_add (x:vec128) (y:vec128) : Lemma
  (ensures cl_add x y == to_vec128 (add (of_vec128 x) (of_vec128 y)))

let lemma_cl_add x y =
  lemma_add_vec128 x y;
  ()

inline_for_extraction
let clmul_wide (x:vec128) (y:vec128) : Tot (vec128 & vec128) =
  let lo = vec_clmul_lo_lo x y in
  let m1 = vec_clmul_hi_lo x y in
  let m2 = vec_clmul_lo_hi x y in
  let hi = vec_clmul_hi_hi x y in
  let m1 = cl_add m1 m2 in
  let m2 = vec_shift_left m1 64ul in
  let m1 = vec_shift_right m1 64ul in
  let lo = cl_add lo m2 in
  let hi = cl_add hi m1 in
  (hi,lo)

val lemma_clmul_wide (x:vec128) (y:vec128) : Lemma
  (ensures (
    let (hi, lo) = clmul_wide x y in
    mul (of_vec128 x) (of_vec128 y) == add (shift (of_vec128 hi) 128) (of_vec128 lo)
  ))

let lemma_clmul_wide x y =
  (* vec128 variables *)
  let lo = vec_clmul_lo_lo x y in
  let m1 = vec_clmul_hi_lo x y in
  let m2 = vec_clmul_lo_hi x y in
  let hi = vec_clmul_hi_hi x y in
  let m12 = cl_add m1 m2 in
  let m12_0 = vec_shift_left m12 64ul in
  let m12_1 = vec_shift_right m12 64ul in
  let lo_m = cl_add lo m12_0 in
  let hi_m = cl_add hi m12_1 in
  (* poly variables *)
  let ab = of_vec128 x in
  let cd = of_vec128 y in
  let n = monomial 64 in
  let a = div ab n in
  let b = mod ab n in
  let c = div cd n in
  let d = mod cd n in
  let ac = mul a c in
  let ad = mul a d in
  let bc = mul b c in
  let bd = mul b d in
  (* vec128 lemmas *)
  vec_clmul_lo_lo_lemma x y;
  vec_clmul_hi_lo_lemma x y;
  vec_clmul_lo_hi_lemma x y;
  vec_clmul_hi_hi_lemma x y;
  lemma_cl_add m1 m2;
  lemma_vec128_double_shift (of_vec128 m12);
  lemma_cl_add lo m12_0;
  lemma_cl_add hi m12_1;
  (* poly lemmas *)
  lemma_shift_is_div ab 64;
  lemma_shift_is_div cd 64;
  lemma_div_distribute ad bc n;
  lemma_add_commute (div ad n) (div bc n);
  lemma_add_associate ac (div bc n) (div ad n);
  lemma_mod_distribute ad bc n;
  lemma_mul_commute (add (mod ad n) (mod bc n)) n;
  lemma_mul_distribute n (mod ad n) (mod bc n);
  lemma_mul_commute n (mod ad n);
  lemma_mul_commute n (mod bc n);
  lemma_add_commute (mul (mod ad n) n) (mul (mod bc n) n);
  lemma_add_commute bd (add (mul (mod bc n) n) (mul (mod ad n) n));
  assert (add (add ac (div bc n)) (div ad n) == of_vec128 hi_m); //OBSERVE
  assert (add (add (mul (mod bc n) n) (mul (mod ad n) n)) bd == of_vec128 lo_m); //OBSERVE
  lemma_split_define ab 64;
  lemma_split_define cd 64;
  lemma_gf128_mul a b c d 64;
  ()

inline_for_extraction
let clmul_wide4
  (x1:vec128) (x2:vec128) (x3:vec128) (x4:vec128)
  (y1:vec128) (y2:vec128) (y3:vec128) (y4:vec128): Tot (vec128 & vec128) =

  let lo1 = vec_clmul_lo_lo x1 y1 in
  let lo2 = vec_clmul_lo_lo x2 y2 in
  let lo3 = vec_clmul_lo_lo x3 y3 in
  let lo4 = vec_clmul_lo_lo x4 y4 in
  let lo = cl_add lo1 lo2 in
  let lo = cl_add lo lo3 in
  let lo = cl_add lo lo4 in

  let m1 = vec_clmul_hi_lo x1 y1 in
  let m2 = vec_clmul_hi_lo x2 y2 in
  let m3 = vec_clmul_hi_lo x3 y3 in
  let m4 = vec_clmul_hi_lo x4 y4 in
  let m = cl_add m1 m2 in
  let m = cl_add m m3 in
  let m = cl_add m m4 in

  let m1 = vec_clmul_lo_hi x1 y1 in
  let m2 = vec_clmul_lo_hi x2 y2 in
  let m3 = vec_clmul_lo_hi x3 y3 in
  let m4 = vec_clmul_lo_hi x4 y4 in
  let m = cl_add m m1 in
  let m = cl_add m m2 in
  let m = cl_add m m3 in
  let m = cl_add m m4 in

  let hi1 = vec_clmul_hi_hi x1 y1 in
  let hi2 = vec_clmul_hi_hi x2 y2 in
  let hi3 = vec_clmul_hi_hi x3 y3 in
  let hi4 = vec_clmul_hi_hi x4 y4 in
  let hi = cl_add hi1 hi2 in
  let hi = cl_add hi hi3 in
  let hi = cl_add hi hi4 in

  let m1 = vec_shift_left m 64ul in
  let m2 = vec_shift_right m 64ul in
  let lo = cl_add lo m1 in
  let hi = cl_add hi m2 in
  (hi, lo)


// inline_for_extraction
// let vec128_shift_left_bits (x:vec128) (y:size_t): Tot vec128 =
//   if (y %. size 8 =. size 0) then
//     vec128_shift_left x y
//   else if (y <. size 64) then
//     let x1 = vec128_shift_right64 x (size 64 -. y) in
//     let x2 = vec128_shift_left64 x y in
//     let x3 = vec128_shift_left x1 (size 64) in
//     let x4 = vec128_or x3 x2 in
//     x4
//   else
//     let x1 = vec128_shift_left64 x (y -. size 64) in
//     let x2 = vec128_shift_left x1 (size 64) in
//     x2


// inline_for_extraction
// let vec128_shift_right_bits (x:vec128) (y:size_t) : Tot vec128 =
//   if (y %. size 8 =. size 0) then
//     vec128_shift_right x y
//   else if (y <. size 64) then
//     let x1 = vec128_shift_left64 x (size 64 -. y) in
//     let x2 = vec128_shift_right64 x y in
//     let x3 = vec128_shift_right x1 (size 64) in
//     let x4 = vec128_or x3 x2 in
//     x4
//   else
//     let x1 = vec128_shift_right64 x (y -. size 64) in
//     let x2 = vec128_shift_right x1 (size 64) in
//     x2


inline_for_extraction
let gf128_reduce (hi:vec128) (lo:vec128) : Tot vec128 =
  (* LEFT SHIFT [hi:lo] by 1 *)
  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) 63ul) in
  let lo2 = vec_shift_left lo1 64ul in
  let lo3 = cast U128 1 (vec_shift_left (cast U64 2 lo) 1ul) in
  let lo3 = vec_xor lo3 lo2 in

  let hi1 = cast U128 1 (vec_shift_right (cast U64 2 hi) 63ul) in
  let hi1 = vec_shift_left hi1 64ul in
  let hi2 = cast U128 1 (vec_shift_left (cast U64 2 hi) 1ul) in
  let hi2 = vec_xor hi2 hi1 in

  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) 63ul) in
  let lo1 = vec_shift_right lo1 64ul in
  let hi2 = vec_xor hi2 lo1 in

  let lo = lo3 in
  let hi = hi2 in
(*
    let lo1 = vec128_shift_right_bits lo (size 127) in
    let lo = vec128_shift_left_bits lo (size 1) in
    let hi = vec128_shift_left_bits hi (size 1) in
    let hi = vec128_xor hi lo1 in
*)
  (* LEFT SHIFT [x0:0] BY 63,62,57 and xor with [x1:x0] *)
  let lo1 = cast U128 1 (vec_shift_left (cast U64 2 lo) 63ul) in
  let lo2 = cast U128 1 (vec_shift_left (cast U64 2 lo) 62ul) in
  let lo3 = cast U128 1 (vec_shift_left (cast U64 2 lo) 57ul) in
  let lo1 = vec_xor lo1 lo2 in
  let lo1 = vec_xor lo1 lo3 in
  let lo2 = vec_shift_right lo1 64ul in
  let lo3 = vec_shift_left lo1 64ul in
  let lo =  vec_xor lo lo3 in
  let lo' = lo2 in

  (* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] *)
  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) 1ul) in
  let lo2 = cast U128 1 (vec_shift_right (cast U64 2 lo) 2ul) in
  let lo3 = cast U128 1 (vec_shift_right (cast U64 2 lo) 7ul) in
  let lo1 = vec_xor lo1 lo2 in
  let lo1 = vec_xor lo1 lo3 in

  let lo1 = vec_xor lo1 lo' in
  let lo = vec_xor lo lo1 in

  let lo = vec_xor lo hi in
  lo


val gf128_clmul_wide_reduce_lemma: x:vec128 -> y:vec128 -> Lemma
  (let (hi, lo) = clmul_wide x y in
   to_elem (gf128_reduce hi lo) == GF.fmul_be #S.gf128 (to_elem x) (to_elem y))
let gf128_clmul_wide_reduce_lemma x y = admit()


val gf128_clmul_wide4_reduce_lemma:
    x1:vec128 -> x2:vec128 -> x3:vec128 -> x4:vec128
  -> y1:vec128 -> y2:vec128 -> y3:vec128 -> y4:vec128 -> Lemma
  (let (hi, lo) = clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 in
   to_elem (gf128_reduce hi lo) == Vec.normalize4 (to_elem4 y1 y2 y3 y4) (to_elem4 x1 x2 x3 x4))
let gf128_clmul_wide4_reduce_lemma x1 x2 x3 x4 y1 y2 y3 y4 = admit()
