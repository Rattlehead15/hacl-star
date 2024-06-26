module Hacl.Spec.Gf128.CT64

open FStar.Mul
open Lib.IntTypes
open Lib.IntVector
open Lib.Buffer
open Lib.ByteBuffer

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec
module Lemmas = Hacl.Spec.GF128.Lemmas

inline_for_extraction noextract
let br_rms (x:uint64) (m:uint64) (s:shiftval U32) : uint64 =
  ((x &. m) <<. s) |. ((x >>. s) &. m)

inline_for_extraction
let br_rev64 (x:uint64) : uint64 =
  let x = br_rms x (u64 0x5555555555555555) (1ul) in
  let x = br_rms x (u64 0x3333333333333333) (2ul) in
  let x = br_rms x (u64 0x0F0F0F0F0F0F0F0F) (4ul) in
  let x = br_rms x (u64 0x00FF00FF00FF00FF) (8ul) in
  let x = br_rms x (u64 0x0000FFFF0000FFFF) (16ul) in
  (x <<. 32ul) |. (x >>. 32ul)

inline_for_extraction noextract
let br_bmul64 (x:uint64) (y:uint64) : uint64 =
  let x0 = x &. (u64 0x1111111111111111) in
  let x1 = x &. (u64 0x2222222222222222) in
  let x2 = x &. (u64 0x4444444444444444) in
  let x3 = x &. (u64 0x8888888888888888) in
  let y0 = y &. (u64 0x1111111111111111) in
  let y1 = y &. (u64 0x2222222222222222) in
  let y2 = y &. (u64 0x4444444444444444) in
  let y3 = y &. (u64 0x8888888888888888) in
  let z0 = (x0 *. y0) ^. (x1 *. y3) ^. (x2 *. y2) ^. (x3 *. y1) in
  let z1 = (x0 *. y1) ^. (x1 *. y0) ^. (x2 *. y3) ^. (x3 *. y2) in
  let z2 = (x0 *. y2) ^. (x1 *. y1) ^. (x2 *. y0) ^. (x3 *. y3) in
  let z3 = (x0 *. y3) ^. (x1 *. y2) ^. (x2 *. y1) ^. (x3 *. y0) in
  (z0 &. (u64 0x1111111111111111)) 
    |. (z1 &. (u64 0x2222222222222222))
    |. (z2 &. (u64 0x4444444444444444))
    |. (z3 &. (u64 0x8888888888888888))

open Lib.Sequence

let elem_s = lseq uint64 2
let elem4_s = lseq uint64 8
let precomp_s = lseq uint64 16

let to_elem (x:elem_s) : S.elem =
  mk_int #U128 (v x.[0] + v x.[1] * pow2 64)

let to_elem_128 (x1 x2:uint64) : S.elem =
  mk_int #U128 (v x1 + v x2 * pow2 64)

let to_elem4 (x:elem4_s) : Vec.elem4 =
  create4 (mk_int #U128 (v x.[0] + v x.[1] * pow2 64))
    (mk_int #U128 (v x.[2] + v x.[3] * pow2 64))
    (mk_int #U128 (v x.[4] + v x.[5] * pow2 64))
    (mk_int #U128 (v x.[6] + v x.[7] * pow2 64))

let fadd_s (x:elem_s) (y:elem_s) : elem_s =
  let r0 = x.[0] ^. y.[0] in
  let r1 = x.[1] ^. y.[1] in
  create2 r0 r1

val fadd_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (fadd_s x y) == GF.fadd (to_elem x) (to_elem y))
let fadd_lemma x y = Lemmas.logxor_s_lemma x y

let br_add4 (x:elem_s) (y:elem_s) : elem_s =
  let r0 = x.[0] ^. y.[0] in
  let r1 = x.[1] ^. y.[1] in
  create2 r0 r1

val br_add4_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (br_add4 x y) == GF.fadd (to_elem x) (to_elem y))
let br_add4_lemma x y = Lemmas.logxor_s_lemma x y

inline_for_extraction
let br_bmul256 (y1 y2 h1 h2 h3 h1r h2r h3r:uint64) : Tot(uint64 & uint64 & uint64 & uint64) =
  let y1r = br_rev64 y1 in
  let y2r = br_rev64 y2 in
  let y3 = y1 ^. y2 in
  let y3r = y1r ^. y2r in
  let z0 = br_bmul64 y1 h1 in
  let z1 = br_bmul64 y2 h2 in
  let z2 = br_bmul64 y3 h3 in
  let z0h = br_bmul64 y1r h1r in
  let z1h = br_bmul64 y2r h2r in
  let z2h = br_bmul64 y3r h3r in
  let z2 = z2 ^. z0 ^. z1 in
  let z2h = z2h ^. z0h ^. z1h in
  let z0h = (br_rev64 z0h) >>. 1ul in
  let z1h = (br_rev64 z1h) >>. 1ul in
  let z2h = (br_rev64 z2h) >>. 1ul in
  (z0, (z0h ^. z2), (z1 ^. z2h), z1h)

inline_for_extraction
let br_reduce (z1 z2 z3 z4:uint64) : Tot(uint64 & uint64) =
  let v3 = (z4 <<. 1ul) |. (z3 >>. 63ul) in
  let v2 = (z3 <<. 1ul) |. (z2 >>. 63ul) in
  let v1 = (z2 <<. 1ul) |. (z1 >>. 63ul) in
  let v0 = z1 <<. 1ul in
  let v2 = v2 ^. v0 ^. (v0 >>. 1ul) ^. (v0 >>. 2ul) ^. (v0 >>. 7ul) in
  let v1 = v1 ^. (v0 <<. 63ul) ^. (v0 <<. 62ul) ^. (v0 <<. 57ul) in
  let v3 = v3 ^. v1 ^. (v1 >>. 1ul) ^. (v1 >>. 2ul) ^. (v1 >>. 7ul) in
  let v2 = v2 ^. (v1 <<. 63ul) ^. (v1 <<. 62ul) ^. (v1 <<. 57ul) in
  (v2, v3)

inline_for_extraction
let br_bmul128 (y1 y2 h1 h2 h3 h1r h2r h3r:uint64) : Tot(uint64 & uint64) =
  let (z1, z2, z3, z4) = br_bmul256 y1 y2 h1 h2 h3 h1r h2r h3r in
  br_reduce z1 z2 z3 z4

val br_bmul128_reduce_lemma: x:elem_s -> y:elem_s -> Lemma
  (let (v1, v2) = br_bmul128 x.[0] x.[1] y.[0] y.[1] (y.[0] ^. y.[1])
      (br_rev64 y.[0]) (br_rev64 y.[1]) ((br_rev64 y.[0]) ^. (br_rev64 y.[1])) in
    to_elem_128 v1 v2 == GF.fmul_be #S.gf128 (to_elem x) (to_elem y))
let br_bmul128_reduce_lemma x y = admit()

let br_bmul256_reduce4 (x:elem4_s) (pre:precomp_s) : Tot(uint64 & uint64) =
  let (x1_1, x1_2, x1_3, x1_4) = br_bmul256 x.[0] x.[1] pre.[0] pre.[1] (pre.[0] ^. pre.[1]) 
    pre.[8] pre.[9] ((pre.[8]) ^. (pre.[9])) in
  let (x2_1, x2_2, x2_3, x2_4) = br_bmul256 x.[2] x.[3] pre.[2] pre.[3] (pre.[2] ^. pre.[3]) 
    pre.[10] pre.[11] ((pre.[10]) ^. (pre.[11])) in
  let (x3_1, x3_2, x3_3, x3_4) = br_bmul256 x.[4] x.[5] pre.[4] pre.[5] (pre.[4] ^. pre.[5]) 
    pre.[12] pre.[13] ((pre.[12]) ^. (pre.[13])) in
  let (x4_1, x4_2, x4_3, x4_4) = br_bmul256 x.[6] x.[7] pre.[6] pre.[7] (pre.[6] ^. pre.[7]) 
    pre.[14] pre.[15] ((pre.[14]) ^. (pre.[15])) in
  br_reduce (x1_1 ^. x2_1 ^. x3_1 ^. x4_1) (x1_2 ^. x2_2 ^. x3_2 ^. x4_2)
    (x1_3 ^. x2_3 ^. x3_3 ^. x4_3) (x1_4 ^. x2_4 ^. x3_4 ^. x4_4)

val br_bmul256_reduce4_lemma:
    x:elem4_s -> pre:precomp_s -> Lemma
   (requires pre.[8] == br_rev64 pre.[0] /\ pre.[9] == br_rev64 pre.[1] /\
            pre.[10] == br_rev64 pre.[2] /\ pre.[11] == br_rev64 pre.[3] /\
            pre.[12] == br_rev64 pre.[4] /\ pre.[13] == br_rev64 pre.[5] /\
            pre.[14] == br_rev64 pre.[6] /\ pre.[15] == br_rev64 pre.[7])
   (ensures (let (v1, v2) = br_bmul256_reduce4 x pre in
            to_elem_128 v1 v2 == Vec.normalize4 (to_elem4 (sub pre 0 8)) (to_elem4 x)))
let br_bmul256_reduce4_lemma x pre = admit()
