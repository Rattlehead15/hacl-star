module Vale.Def.Types_helpers_BE

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open FStar.Math.Lemmas
open Vale.Lib.Seqs
open Vale.Lib.Seqs_s
open Vale.Def.Words.Seq

unfold let pow2_24 = 0x1000000
let nat24 = natN pow2_24

val seq_four_to_seq_to_seq_four_BE (#a:Type) (x:seq a{length x % 4 == 0}) :
  Lemma (seq_four_to_seq_BE (seq_to_seq_four_BE x) == x)
  [SMTPat (seq_four_to_seq_BE (seq_to_seq_four_BE x))]

val be_quad32_to_bytes_to_quad32 (s:seq nat8 { length s == 16 }) :
  Lemma(be_quad32_to_bytes (be_bytes_to_quad32 s) == s)

val be_bytes_to_seq_quad32_to_bytes (s:seq quad32) :
  Lemma (be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) == s)

val four_to_seq_BE_is_seq_four_to_seq_BE (x:four nat32) :
  Lemma (four_to_seq_BE x == seq_four_to_seq_BE (create 1 x))

val be_bytes_to_seq_quad32_to_bytes_one_quad (b:quad32) :
  Lemma (be_bytes_to_seq_quad32 (be_quad32_to_bytes b) == create 1 b)

val append_distributes_seq_to_seq_four_BE (#a:Type) (x:seq a{length x % 4 == 0}) (y:seq a{length y % 4 == 0}) :
  Lemma (seq_to_seq_four_BE (x @| y) == seq_to_seq_four_BE x @| seq_to_seq_four_BE y)

val append_distributes_be_bytes_to_seq_quad32 (s1:seq nat8 { length s1 % 16 == 0 }) (s2:seq nat8 { length s2 % 16 == 0 }) :
  Lemma(be_bytes_to_seq_quad32 (s1 @| s2) == (be_bytes_to_seq_quad32 s1) @| (be_bytes_to_seq_quad32 s2))

val seq_to_four_BE_is_seq_to_seq_four_BE (#a:Type) (s:seq4 a) : Lemma
  (create 1 (seq_to_four_BE s) == seq_to_seq_four_BE s)

val be_bytes_to_seq_quad_of_singleton (q:quad32) (b:seq nat8 { length b == 16 }) : Lemma
  (requires q == be_bytes_to_quad32 b)
  (ensures create 1 q == be_bytes_to_seq_quad32 b)

val slice_commutes_seq_four_to_seq_BE (#a:Type) (s:seq (four a)) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (seq_four_to_seq_BE s) (n * 4) (n' * 4) ==
        seq_four_to_seq_BE (slice s n n'))

val slice_commutes_be_seq_quad32_to_bytes (s:seq quad32) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (n * 16) (n' * 16) ==
        seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice s n n')))

val lemma_slices_be_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = be_quad32_to_bytes q in
    q.hi3 == four_to_nat 8 (seq_to_four_BE (slice s 0 4)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_BE (slice s 4 8)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_BE (slice s 8 12)) /\
    q.lo0 == four_to_nat 8 (seq_to_four_BE (slice s 12 16))
  ))

val be_seq_quad32_to_bytes_of_singleton (q:quad32) :
  Lemma (be_quad32_to_bytes q == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 q)))

val slice_commutes_be_seq_quad32_to_bytes0 (s:seq quad32) (n:nat{n <= length s}) :
  Lemma(slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 (n * 16) ==
        seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice s 0 n)))

val lemma_be_seq_quad32_to_bytes_length (s:seq quad32) :
  Lemma(length (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) == (length s) * 16)

val be_bytes_to_seq_quad32_empty: unit ->
  Lemma (forall s . {:pattern (length (be_bytes_to_seq_quad32 s)) } length s == 0 ==> length (be_bytes_to_seq_quad32 s) == 0)

val seq_nat8_to_seq_nat32_to_seq_nat8_BE (x:seq nat32) :
  Lemma (seq_nat8_to_seq_nat32_BE (seq_nat32_to_seq_nat8_BE x) == x)
  [SMTPat (seq_nat8_to_seq_nat32_BE (seq_nat32_to_seq_nat8_BE x))]

val append_distributes_seq_four_to_seq_BE (#a:Type) (x:seq (four a)) (y:seq (four a)) :
  Lemma (seq_four_to_seq_BE (x @| y) == seq_four_to_seq_BE x @| seq_four_to_seq_BE y)

val append_distributes_be_seq_quad32_to_bytes (s1:seq quad32) (s2:seq quad32) :
  Lemma(seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (s1 @| s2)) == (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s1)) @| (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s2)))

val seq_four_to_seq_BE_injective (a:eqtype) : Lemma
  (forall (x x':seq (four a)).{:pattern seq_four_to_seq_BE x; seq_four_to_seq_BE x'}
    seq_four_to_seq_BE x == seq_four_to_seq_BE x' ==> x == x')

val seq_four_to_seq_BE_injective_specific (#a:eqtype) (x x':seq (four a)) :
  Lemma (seq_four_to_seq_BE x == seq_four_to_seq_BE x' ==> x == x')

val four_to_seq_BE_injective (a:eqtype) : Lemma
  (forall (x x':four a).{:pattern four_to_seq_BE x; four_to_seq_BE x'}
    four_to_seq_BE x == four_to_seq_BE x' ==> x == x')

val be_quad32_to_bytes_injective: unit ->
  Lemma (forall b b' . be_quad32_to_bytes b == be_quad32_to_bytes b' ==> b == b')

val be_quad32_to_bytes_injective_specific (b b':quad32) :
  Lemma (be_quad32_to_bytes b == be_quad32_to_bytes b' ==> b == b')

val lemma_BitwiseXorWithZero64 (n:nat64) : Lemma (ixor n 0 == n)

let lemma_ishl_64 (x:nat64) (k:nat) : Lemma
  (ensures ishl #pow2_64 x k == x * pow2 k % pow2_64)
  =
  Vale.Def.TypesNative_s.reveal_ishl 64 x k;
  FStar.UInt.shift_left_value_lemma #64 x k;
  ()

let lemma_ishr_64 (x:nat64) (k:nat) : Lemma
  (ensures ishr #pow2_64 x k == x / pow2 k)
  =
  Vale.Def.TypesNative_s.reveal_ishr 64 x k;
  FStar.UInt.shift_right_value_lemma #64 x k;
  ()

let lemma_ishr_32 (x:nat32) (k:nat) : Lemma
  (ensures ishr #pow2_32 x k == x / pow2 k)
  =
  Vale.Def.TypesNative_s.reveal_ishr 32 x k;
  FStar.UInt.shift_right_value_lemma #32 x k;
  ()
