module Hacl.Impl.Gf128.CT64

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec
module CT64 = Hacl.Spec.Gf128.CT64
module Lemmas = Hacl.Spec.GF128.Lemmas


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

noextract
let zero = GF.zero #S.gf128

inline_for_extraction noextract
let bit_mask64 (u:uint64) = u64 0 -. (u &. u64 1)

type felem = lbuffer uint64 2ul
type felem4 = lbuffer uint64 8ul
type precomp = lbuffer uint64 16ul

type block = lbuffer uint8 16ul
type block4 = lbuffer uint8 64ul


unfold noextract
let op_String_Access #a #len = LSeq.index #a #len


noextract
let feval (h:mem) (f:felem) : GTot Vec.elem =
  let f = as_seq h f in
  uint #U128 #SEC (v f.[1] * pow2 64 + v f.[0])


noextract
let feval4 (h:mem) (f:felem4) : GTot Vec.elem4 =
  let f = as_seq h f in
  let f0 = uint #U128 #SEC (v f.[1] * pow2 64 + v f.[0]) in
  let f1 = uint #U128 #SEC (v f.[3] * pow2 64 + v f.[2]) in
  let f2 = uint #U128 #SEC (v f.[5] * pow2 64 + v f.[4]) in
  let f3 = uint #U128 #SEC (v f.[7] * pow2 64 + v f.[6]) in
  LSeq.create4 f0 f1 f2 f3

noextract
let load_precomp_r_inv (h:mem) (pre:precomp) : Type0 =
  let pre_r = Vec.load_precompute_r (feval h (gsub pre 6ul 2ul)) in
  feval4 h (gsub pre 0ul 8ul) == pre_r /\
  feval h (gsub pre 8ul 2ul) == LSeq.create2 (CT64.br_rev64 pre_r.[size 0]) (CT64.br_rev64 pre_r.[size 1]) /\
  feval h (gsub pre 10ul 2ul) == LSeq.create2 (CT64.br_rev64 pre_r.[size 2]) (CT64.br_rev64 pre_r.[size 3]) /\
  feval h (gsub pre 12ul 2ul) == LSeq.create2 (CT64.br_rev64 pre_r.[size 4]) (CT64.br_rev64 pre_r.[size 5]) /\
  feval h (gsub pre 14ul 2ul) == LSeq.create2 (CT64.br_rev64 pre_r.[size 6]) (CT64.br_rev64 pre_r.[size 7])

inline_for_extraction noextract
val create_felem: unit ->
  StackInline felem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 2 (u64 0)) /\
    feval h1 f == zero)

let create_felem () = create 2ul (u64 0)

inline_for_extraction noextract
val felem_set_zero: f:felem ->
  Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies1 f h0 h1 /\
    feval h1 f == zero)

let felem_set_zero f =
  f.(0ul) <- u64 0;
  f.(1ul) <- u64 0

inline_for_extraction noextract
val copy_felem: f1:felem -> f2:felem ->
  Stack unit
  (requires fun h -> live h f1 /\ live h f2 /\ eq_or_disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies1 f1 h0 h1 /\
    as_seq h1 f1 == as_seq h0 f2)

let copy_felem f1 f2 =
  let h0 = ST.get () in
  f1.(0ul) <- f2.(0ul);
  f1.(1ul) <- f2.(1ul);
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 f1) (as_seq h0 f2)

inline_for_extraction noextract
val create_felem4: unit ->
  StackInline felem4
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 8 (u64 0)) /\
    feval4 h1 f == LSeq.create 4 zero)

let create_felem4 () =
  let f = create 8ul (u64 0) in
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 f) (LSeq.create 4 (u128 0));
  f

inline_for_extraction noextract
val load_felem:
    x:felem
  -> y:block ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == S.encode (as_seq h0 y))

let load_felem x y =
  let h0 = ST.get () in
  assert (S.encode (as_seq h0 y) == BSeq.uint_from_bytes_be #U128 #SEC (as_seq h0 y));
  x.(size 1) <- uint_from_bytes_be #U64 (sub y (size 0) (size 8));
  x.(size 0) <- uint_from_bytes_be #U64 (sub y (size 8) (size 8));
  let h1 = ST.get () in
  assert (feval h1 x == uint #U128 #SEC (v (as_seq h1 x).[1] * pow2 64 + v (as_seq h1 x).[0]));
  BSeq.lemma_reveal_uint_to_bytes_be #U64 (LSeq.sub (as_seq h0 y) 0 8);
  BSeq.lemma_reveal_uint_to_bytes_be #U64 (LSeq.sub (as_seq h0 y) 8 8);
  assert (v (feval h1 x) == BSeq.nat_from_bytes_be (LSeq.sub (as_seq h0 y) 8 8) + pow2 64 * BSeq.nat_from_bytes_be (LSeq.sub (as_seq h0 y) 0 8));
  BSeq.nat_from_intseq_be_slice_lemma (as_seq h0 y) 8;
  assert (v (feval h1 x) == BSeq.nat_from_bytes_be (as_seq h0 y));
  BSeq.lemma_reveal_uint_to_bytes_be #U128 (as_seq h0 y);
  assert (v (feval h1 x) == v (S.encode (as_seq h0 y)))

inline_for_extraction noextract
val load_felem4:
    x:felem4
  -> y:block4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.encode4 (as_seq h0 y))

let load_felem4 x y =
  let x0 = sub x (size 0) (size 2) in
  let y0 = sub y (size 0) (size 16) in
  let x1 = sub x (size 2) (size 2) in
  let y1 = sub y (size 16) (size 16) in
  let x2 = sub x (size 4) (size 2) in
  let y2 = sub y (size 32) (size 16) in
  let x3 = sub x (size 6) (size 2) in
  let y3 = sub y (size 48) (size 16) in
  load_felem x0 y0;
  load_felem x1 y1;
  load_felem x2 y2;
  load_felem x3 y3

val uints64_to_bytes_be_lemma: lo:uint64 -> hi:uint64 -> Lemma
  (LSeq.concat (BSeq.uint_to_bytes_be lo) (BSeq.uint_to_bytes_be hi) == BSeq.nat_to_bytes_be 16 (v lo * pow2 64 + v hi))
let uints64_to_bytes_be_lemma lo hi =
  let open Lib.ByteSequence in
  let lp = nat_to_bytes_be #SEC 16 (v lo * pow2 64 + v hi) in
  let rp = LSeq.concat (uint_to_bytes_be lo) (uint_to_bytes_be hi) in
  assert (nat_from_bytes_be lp == v lo * pow2 64 + v hi);
  Seq.append_slices (uint_to_bytes_be lo) (uint_to_bytes_be hi);
  nat_from_intseq_be_slice_lemma #U8 #SEC #16 rp 8;
  assert (nat_from_bytes_be rp == nat_from_bytes_be (LSeq.sub rp 8 8) + pow2 (8 * 8) * nat_from_bytes_be (LSeq.sub rp 0 8));
  assert (nat_from_bytes_be rp == nat_from_bytes_be (uint_to_bytes_be hi) + pow2 64 * nat_from_bytes_be (uint_to_bytes_be lo));
  lemma_uint_to_bytes_be_preserves_value lo;
  lemma_uint_to_bytes_be_preserves_value hi;
  nat_from_intseq_be_inj lp rp

inline_for_extraction noextract
val store_felem:
    x:lbuffer uint8 16ul
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    as_seq h1 x == S.store_elem (feval h0 y))

let store_felem x y =
  let h0 = ST.get () in
  assert (S.store_elem (feval h0 y) == BSeq.uint_to_bytes_be #U128 #SEC (feval h0 y));
  let h0 = ST.get () in
  let r0 = y.(1ul) in
  let r1 = y.(0ul) in
  update_sub_f h0 x 0ul 8ul
    (fun h -> BSeq.uint_to_bytes_be #U64 r0)
    (fun _ -> uint_to_bytes_be (sub x 0ul 8ul) r0);
  let h1 = ST.get () in
  update_sub_f h1 x 8ul 8ul
    (fun h -> BSeq.uint_to_bytes_be #U64 r1)
    (fun _ -> uint_to_bytes_be (sub x 8ul 8ul) r1);
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h2 x) 0 8) (BSeq.uint_to_bytes_be #U64 r0);
  LSeq.lemma_concat2 8 (BSeq.uint_to_bytes_be #U64 r0) 8 (BSeq.uint_to_bytes_be #U64 r1) (as_seq h2 x);
  uints64_to_bytes_be_lemma r0 r1;
  assert (as_seq h2 x == BSeq.nat_to_bytes_be 16 (v (feval h0 y)));
  BSeq.lemma_nat_to_from_bytes_be_preserves_value (as_seq h2 x) 16 (v (feval h0 y));
  BSeq.lemma_uint_to_bytes_be_preserves_value (feval h0 y);
  BSeq.nat_from_intseq_be_inj (as_seq h2 x) (BSeq.uint_to_bytes_be #U128 #SEC (feval h0 y))

inline_for_extraction noextract
val fadd:
    x:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fadd #S.gf128 (feval h0 x) (feval h0 y))

let fadd x y =
  let h0 = ST.get () in
  x.(size 0) <- x.(size 0) ^. y.(size 0);
  x.(size 1) <- x.(size 1) ^. y.(size 1);
  CT64.fadd_lemma (as_seq h0 x) (as_seq h0 y)


inline_for_extraction noextract
val fadd4:
    x:felem4
  -> y:felem4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.fadd4 (feval4 h0 x) (feval4 h0 y))

let fadd4 x y =
  let x0 = sub x (size 0) (size 2) in
  let y0 = sub y (size 0) (size 2) in
  let x1 = sub x (size 2) (size 2) in
  let y1 = sub y (size 2) (size 2) in
  let x2 = sub x (size 4) (size 2) in
  let y2 = sub y (size 4) (size 2) in
  let x3 = sub x (size 6) (size 2) in
  let y3 = sub y (size 6) (size 2) in

  let h0 = ST.get () in
  fadd x0 y0;
  fadd x1 y1;
  fadd x2 y2;
  fadd x3 y3;
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 x) (Vec.fadd4 (feval4 h0 x) (feval4 h0 y))

val fmul:
    x:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 y))

[@ CInline]
let fmul x y =
  let h0 = ST.get () in
  let yr1 = CT64.br_rev64 y.(size 0) in
  let yr2 = CT64.br_rev64 y.(size 1) in
  let (x1, x2) = CT64.br_bmul128 x.(size 0) x.(size 1)
    y.(size 0) y.(size 1) (y.(size 0) ^. y.(size 1))  yr1 yr2 (yr1 ^. yr2) in
  x.(size 0) <- x1;
  x.(size 1) <- x2;
  CT64.br_bmul128_reduce_lemma (as_seq h0 x) (as_seq h0 y)

val load_precompute_r:
    pre:precomp
  -> key:block ->
  Stack unit
  (requires fun h -> live h pre /\ live h key /\ disjoint pre key)
  (ensures  fun h0 _ h1 -> modifies1 pre h0 h1 /\
    feval h1 (gsub pre 24ul 2ul) == S.load_elem (as_seq h0 key) /\
    load_precomp_r_inv h1 pre)

[@CInline]
let load_precompute_r pre key =
  let h1_0 = sub pre (size 6) (size 2) in
  let h2_0 = sub pre (size 4) (size 2) in
  let h3_0 = sub pre (size 2) (size 2) in
  let h4_0 = sub pre (size 0) (size 2) in
  load_felem h1_0 key;
  copy_felem h2_0 h1_0;
  copy_felem h3_0 h1_0;
  copy_felem h4_0 h1_0;

  fmul h2_0 h1_0;
  fmul h3_0 h2_0;
  fmul h4_0 h3_0;

  pre.(size 14) <- CT64.br_rev64 h1_0.(size 0);
  pre.(size 15) <- CT64.br_rev64 h1_0.(size 1);
  pre.(size 12) <- CT64.br_rev64 h2_0.(size 0);
  pre.(size 13) <- CT64.br_rev64 h2_0.(size 1);
  pre.(size 10) <- CT64.br_rev64 h3_0.(size 0);
  pre.(size 11) <- CT64.br_rev64 h3_0.(size 1);
  pre.(size 8) <- CT64.br_rev64 h4_0.(size 0);
  pre.(size 9) <- CT64.br_rev64 h4_0.(size 1)

inline_for_extraction noextract
val fadd_acc4:
    x:felem4
  -> acc:felem ->
  Stack unit
  (requires fun h ->
    live h x /\ live h acc /\ disjoint x acc)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.fadd4 (LSeq.create4 (feval h0 acc) zero zero zero) (feval4 h0 x))

let fadd_acc4 x acc =
  let h0 = ST.get () in
  fadd (sub x 0ul 2ul) acc;
  let h1 = ST.get () in
  assert (feval h1 (gsub x 0ul 2ul) == GF.fadd #S.gf128 (feval h0 (gsub x 0ul 2ul)) (feval h0 acc));
  Lemmas.add_commutativity (feval h0 (gsub x 0ul 2ul)) (feval h0 acc);
  Lemmas.add_identity (feval h0 (gsub x 2ul 2ul));
  Lemmas.add_identity (feval h0 (gsub x 4ul 2ul));
  Lemmas.add_identity (feval h0 (gsub x 6ul 2ul));
  LSeq.eq_intro (feval4 h1 x) (Vec.fadd4 (LSeq.create4 (feval h0 acc) zero zero zero) (feval4 h0 x))

#set-options "--z3rlimit 100"

val normalize4:
    acc:felem
  -> x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h x /\ live h pre /\
    disjoint acc pre /\ disjoint acc x /\ disjoint x pre /\
    load_precomp_r_inv h pre)
  (ensures  fun h0 _ h1 -> modifies2 x acc h0 h1 /\
    feval h1 acc == Vec.normalize4 (feval4 h0 (gsub pre 0ul 8ul)) (feval4 h0 x))

[@CInline]
let normalize4 acc x pre =
  let x1 = sub x (0ul) (2ul) in
  let x2 = sub x (2ul) (2ul) in
  let x3 = sub x (4ul) (2ul) in
  let x4 = sub x (6ul) (2ul) in
  let y1 = sub pre (0ul) (2ul) in
  let y2 = sub pre (2ul) (2ul) in
  let y3 = sub pre (4ul) (2ul) in
  let y4 = sub pre (6ul) (2ul) in
  let yr1 = sub pre (8ul) (2ul) in
  let yr2 = sub pre (10ul) (2ul) in
  let yr3 = sub pre (12ul) (2ul) in
  let yr4 = sub pre (14ul) (2ul) in

  let (z1_1, z1_2, z1_3, z1_4) = CT64.br_bmul256 x1.(size 0) x1.(size 1) 
    y1.(size 0) y1.(size 1) (y1.(size 0) ^. y1.(size 1)) 
    yr1.(size 0) yr1.(size 1) (yr1.(size 0) ^. yr1.(size 1)) in
  let (z2_1, z2_2, z2_3, z2_4) = CT64.br_bmul256 x2.(size 0) x2.(size 1) 
    y2.(size 0) y2.(size 1) (y2.(size 0) ^. y2.(size 1)) 
    yr2.(size 0) yr2.(size 1) (yr2.(size 0) ^. yr2.(size 1)) in
  let z1 = z1_1 ^. z2_1 in
  let z2 = z1_2 ^. z2_2 in
  let z3 = z1_3 ^. z2_3 in
  let z4 = z1_4 ^. z2_4 in
  let (z3_1, z3_2, z3_3, z3_4) = CT64.br_bmul256 x3.(size 0) x3.(size 1) 
    y3.(size 0) y3.(size 1) (y3.(size 0) ^. y3.(size 1)) 
    yr3.(size 0) yr3.(size 1) (yr3.(size 0) ^. yr3.(size 1)) in
  let z1 = z1 ^. z3_1 in
  let z2 = z2 ^. z3_2 in
  let z3 = z3 ^. z3_3 in
  let z4 = z4 ^. z3_4 in
  let (z4_1, z4_2, z4_3, z4_4) = CT64.br_bmul256 x4.(size 0) x4.(size 1) 
    y4.(size 0) y4.(size 1) (y4.(size 0) ^. y4.(size 1)) 
    yr4.(size 0) yr4.(size 1) (yr4.(size 0) ^. yr4.(size 1)) in
  let z1 = z1 ^. z4_1 in
  let z2 = z2 ^. z4_2 in
  let z3 = z3 ^. z4_3 in
  let z4 = z4 ^. z4_4 in

  let (v1, v2) = CT64.br_reduce z1 z2 z3 z4 in
  acc.(size 0) <- v1;
  acc.(size 1) <- v2;
  CT64.br_bmul256_reduce4_lemma x pre
