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
open Vale.Arch.TypesNative
open Vale.Lib.Meta

let seq_four_to_seq_to_seq_four_BE (#a:Type) (x:seq a{length x % 4 == 0}) :
  Lemma (seq_four_to_seq_BE (seq_to_seq_four_BE x) == x)
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #a);
  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #a);
  assert (equal (seq_four_to_seq_BE (seq_to_seq_four_BE x)) x);
  ()

let be_quad32_to_bytes_to_quad32 s =
  calc (==) {
    be_quad32_to_bytes (be_bytes_to_quad32 s);
    == {be_bytes_to_quad32_reveal ()}
    be_quad32_to_bytes (seq_to_four_BE (seq_map (four_to_nat 8) (seq_to_seq_four_BE s)));
    == {reveal_opaque (`%be_quad32_to_bytes) be_quad32_to_bytes}
    seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE (seq_to_four_BE (seq_map (four_to_nat 8) (seq_to_seq_four_BE s)))));
    == {four_to_seq_to_four_BE (seq_map (four_to_nat 8) (seq_to_seq_four_BE s))}
    seq_four_to_seq_BE (seq_map (nat_to_four 8) (seq_map (four_to_nat 8) (seq_to_seq_four_BE s)));
    == {seq_map_inverses (four_to_nat 8) (nat_to_four 8) (seq_to_seq_four_BE s)}
    seq_four_to_seq_BE (seq_to_seq_four_BE s);
    == {}
    s;
  }

let be_bytes_to_seq_quad32_to_bytes (s:seq quad32) :
  Lemma (be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) == s)
  =
  reveal_opaque (`%be_bytes_to_seq_quad32) be_bytes_to_seq_quad32;
  seq_to_seq_four_to_seq_BE (seq_map (nat_to_four 8) (seq_four_to_seq_BE s));
  seq_map_inverses (nat_to_four 8) (four_to_nat 8) (seq_four_to_seq_BE s);
  seq_to_seq_four_to_seq_BE (s) ;
  ()

let four_to_seq_BE_is_seq_four_to_seq_BE (x:four nat32) :
  Lemma (four_to_seq_BE x == seq_four_to_seq_BE (create 1 x))
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #nat32);
  let s0 = four_to_seq_BE x  in
  let s1 = seq_four_to_seq_BE (create 1 x) in
  assert (equal s0 s1);
  ()

let be_bytes_to_seq_quad32_to_bytes_one_quad (b:quad32) =
  calc (==) {
    be_bytes_to_seq_quad32 (be_quad32_to_bytes b);
    == {reveal_opaque (`%be_bytes_to_seq_quad32) be_bytes_to_seq_quad32}
    seq_to_seq_four_BE (seq_nat8_to_seq_nat32_BE (be_quad32_to_bytes b));
    == {reveal_opaque (`%be_quad32_to_bytes) be_quad32_to_bytes}
    seq_to_seq_four_BE (seq_nat8_to_seq_nat32_BE (seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE b))));
    == {}
    seq_to_seq_four_BE (seq_map (four_to_nat 8) (seq_to_seq_four_BE (seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE b)))));
    == {seq_to_seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE b))}
    seq_to_seq_four_BE (seq_map (four_to_nat 8) (seq_map (nat_to_four 8) (four_to_seq_BE b)));
    == {seq_map_inverses (nat_to_four 8) (four_to_nat 8) (four_to_seq_BE b)}
    seq_to_seq_four_BE (four_to_seq_BE b);
    == {four_to_seq_BE_is_seq_four_to_seq_BE b}
    seq_to_seq_four_BE (seq_four_to_seq_BE (create 1 b));
    == {}
    create 1 b;
  }

let append_distributes_seq_to_seq_four_BE (#a:Type) (x:seq a{length x % 4 == 0}) (y:seq a{length y % 4 == 0}) :
  Lemma (seq_to_seq_four_BE (x @| y) == seq_to_seq_four_BE x @| seq_to_seq_four_BE y)
  =
  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #a);
  assert (equal (seq_to_seq_four_BE (x @| y)) (seq_to_seq_four_BE x @| seq_to_seq_four_BE y));
  ()

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq.Properties'"
let append_distributes_be_bytes_to_seq_quad32 (s1:seq nat8 { length s1 % 16 == 0 }) (s2:seq nat8 { length s2 % 16 == 0 }) :
  Lemma(be_bytes_to_seq_quad32 (s1 @| s2) == (be_bytes_to_seq_quad32 s1) @| (be_bytes_to_seq_quad32 s2))
  =
  reveal_opaque (`%be_bytes_to_seq_quad32) be_bytes_to_seq_quad32;
  let s1' = seq_nat8_to_seq_nat32_BE s1 in
  let s2' = seq_nat8_to_seq_nat32_BE s2 in
  append_distributes_seq_to_seq_four_BE s1' s2';
  append_distributes_seq_map (four_to_nat 8) (seq_to_seq_four_BE s1) (seq_to_seq_four_BE s2);
  append_distributes_seq_to_seq_four_BE s1 s2;
  ()

let seq_to_four_BE_is_seq_to_seq_four_BE (#a:Type) (s:seq4 a) : Lemma
  (create 1 (seq_to_four_BE s) == seq_to_seq_four_BE s)
  =
  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #a);
  assert (equal (create 1 (seq_to_four_BE s)) (seq_to_seq_four_BE s));
  ()

let be_bytes_to_seq_quad_of_singleton (q:quad32) (b:seq nat8 { length b == 16 }) : Lemma
  (requires q == be_bytes_to_quad32 b)
  (ensures create 1 q == be_bytes_to_seq_quad32 b)
  =
  reveal_opaque (`%be_bytes_to_seq_quad32) be_bytes_to_seq_quad32;
  be_bytes_to_quad32_reveal ();
  seq_to_four_BE_is_seq_to_seq_four_BE (seq_map (four_to_nat 8) (seq_to_seq_four_BE b));
  ()

let slice_commutes_seq_four_to_seq_BE (#a:Type) (s:seq (four a)) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (seq_four_to_seq_BE s) (n * 4) (n' * 4) ==
        seq_four_to_seq_BE (slice s n n'))
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #a);
  assert (equal (slice (seq_four_to_seq_BE s) (n * 4) (n' * 4))
                (seq_four_to_seq_BE (slice s n n')));
  ()

let slice_commutes_be_seq_quad32_to_bytes (s:seq quad32) (n:nat{n <= length s}) (n':nat{ n <= n' /\ n' <= length s}) :
  Lemma(slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (n * 16) (n' * 16) ==
        seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice s n n')))
  =
  slice_commutes_seq_four_to_seq_BE s n n';
  assert (slice (seq_four_to_seq_BE s) (n * 4) (n' * 4) == seq_four_to_seq_BE (slice s n n'));
  slice_seq_map_commute (nat_to_four 8) (seq_four_to_seq_BE s) (n*4) (n'*4);

  let s_inner = (seq_map (nat_to_four 8) (seq_four_to_seq_BE s)) in
  slice_commutes_seq_four_to_seq_BE s_inner (n * 4) (n' * 4);
  ()

let lemma_slices_be_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = be_quad32_to_bytes q in
    q.hi3 == four_to_nat 8 (seq_to_four_BE (slice s 0 4)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_BE (slice s 4 8)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_BE (slice s 8 12)) /\
    q.lo0 == four_to_nat 8 (seq_to_four_BE (slice s 12 16))
  ))
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #nat8);
  reveal_opaque (`%be_quad32_to_bytes) be_quad32_to_bytes;
  ()

let be_seq_quad32_to_bytes_of_singleton (q:quad32) :
  Lemma (be_quad32_to_bytes q == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 q)))
  =
  reveal_opaque (`%be_quad32_to_bytes) be_quad32_to_bytes;
  four_to_seq_BE_is_seq_four_to_seq_BE q;
  ()

let slice_commutes_be_seq_quad32_to_bytes0 (s:seq quad32) (n:nat{n <= length s}) :
  Lemma(slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 (n * 16) ==
        seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice s 0 n)))
  =
  slice_commutes_be_seq_quad32_to_bytes s 0 n

let lemma_be_seq_quad32_to_bytes_length (s:seq quad32) :
  Lemma(length (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) == (length s) * 16)
  =
  ()

let be_bytes_to_seq_quad32_empty () :
  Lemma (forall s . {:pattern (length (be_bytes_to_seq_quad32 s)) } length s == 0 ==> length (be_bytes_to_seq_quad32 s) == 0)
  =
  reveal_opaque (`%be_bytes_to_seq_quad32) be_bytes_to_seq_quad32;
  ()

let seq_nat8_to_seq_nat32_to_seq_nat8_BE (x:seq nat32) :
  Lemma (seq_nat8_to_seq_nat32_BE (seq_nat32_to_seq_nat8_BE x) == x)
  =
  assert (equal (seq_nat8_to_seq_nat32_BE (seq_nat32_to_seq_nat8_BE x)) x);
  ()

let append_distributes_seq_four_to_seq_BE #a x y =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #a);
  assert (equal (seq_four_to_seq_BE (x @| y)) (seq_four_to_seq_BE x @| seq_four_to_seq_BE y))

let append_distributes_be_seq_quad32_to_bytes s1 s2 =
  calc (==) {
    seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (s1 @| s2));
    (==) { }
    seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (s1 @| s2));
    (==) { append_distributes_seq_four_to_seq_BE s1 s2 }
    seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s1 @| seq_four_to_seq_BE s2);
    (==) { append_distributes_seq_map (nat_to_four 8) (seq_four_to_seq_BE s1) (seq_four_to_seq_BE s2) }
    seq_four_to_seq_BE (
      seq_map (nat_to_four 8) (seq_four_to_seq_BE s1) @|
      seq_map (nat_to_four 8) (seq_four_to_seq_BE s2));
    (==) { append_distributes_seq_four_to_seq_BE
         (seq_map (nat_to_four 8) (seq_four_to_seq_BE s1))
         (seq_map (nat_to_four 8) (seq_four_to_seq_BE s2)) }
      seq_four_to_seq_BE (seq_map (nat_to_four 8) (seq_four_to_seq_BE s1)) @|
      seq_four_to_seq_BE (seq_map (nat_to_four 8) (seq_four_to_seq_BE s2));
    (==) { }
    seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s1) @| seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s2);
  }


let seq_four_to_seq_BE_injective (a:eqtype) :
  Lemma (forall (x x': seq (four a)). seq_four_to_seq_BE #a x == seq_four_to_seq_BE #a x' ==> x == x')
  =
  let seq_four_to_seq_BE_stronger (#b:Type) (x:seq (four b)) : (s:seq b{length s % 4 == 0}) =
    seq_four_to_seq_BE x
  in
  generic_injective_proof (seq_four_to_seq_BE_stronger) (seq_to_seq_four_BE #a) (seq_to_seq_four_to_seq_BE #a);
  ()

let seq_four_to_seq_BE_injective_specific (#a:eqtype) (x x':seq (four a)) :
  Lemma (seq_four_to_seq_BE x == seq_four_to_seq_BE x' ==> x == x')
  =
  seq_four_to_seq_BE_injective a

let four_to_seq_BE_injective (a:eqtype) :
  Lemma (forall (x x': four a) . four_to_seq_BE x == four_to_seq_BE x' ==> x == x')
  =
  generic_injective_proof #(four a) #(seq4 a) (four_to_seq_BE #a) (seq_to_four_BE #a) (seq_to_four_to_seq_BE #a)

let be_quad32_to_bytes_injective ():
  Lemma (forall b b' . be_quad32_to_bytes b == be_quad32_to_bytes b' ==> b == b')
  =
  reveal_opaque (`%be_quad32_to_bytes) be_quad32_to_bytes;
  let helper (b b':quad32) : Lemma (be_quad32_to_bytes b == be_quad32_to_bytes b' ==> b == b') =
    if be_quad32_to_bytes b = be_quad32_to_bytes b' then (
      let b1  = seq_map (nat_to_four 8) (four_to_seq_BE b) in
      let b1' = seq_map (nat_to_four 8) (four_to_seq_BE b') in
      assert (be_quad32_to_bytes b == seq_four_to_seq_BE b1);
      assert (be_quad32_to_bytes b' == seq_four_to_seq_BE b1');
      seq_four_to_seq_BE_injective_specific b1 b1';
      assert (b1 == b1');
      nat_to_four_8_injective();
      seq_map_injective (nat_to_four 8) (four_to_seq_BE b) (four_to_seq_BE b');
      assert ((four_to_seq_BE b) == (four_to_seq_BE b'));
      four_to_seq_BE_injective nat32;
      ()
    ) else
    ()
  in
  FStar.Classical.forall_intro_2 helper

let be_quad32_to_bytes_injective_specific (b b':quad32) :
  Lemma (be_quad32_to_bytes b == be_quad32_to_bytes b' ==> b == b')
  =
  be_quad32_to_bytes_injective()

let lemma_BitwiseXorWithZero64 n =
  lemma_ixor_nth_all 64;
  lemma_zero_nth 64;
  lemma_equal_nth 64 (ixor n 0) n
