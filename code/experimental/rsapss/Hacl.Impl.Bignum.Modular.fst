module Hacl.Impl.Bignum.Modular

open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.Mul

open Lib.IntTypes
open Lib.Math.Algebra
open Lib.Buffer
open Lib.Loops

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Shift
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Openssl
open Hacl.Impl.Bignum.Misc
open Hacl.Impl.Bignum.Multiplication
open Hacl.Impl.Bignum.Addition
open Hacl.Spec.Bignum


val enable_ossl : bool
let enable_ossl = true

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_remainder_core:
     #rLen:bn_len
  -> #modLen:bn_len{v modLen <= v rLen}
  -> r_i:lbignum rLen
  -> mod:lbignum modLen
  -> count:size_t
  -> Stack unit
        (requires (fun h -> live h r_i /\ live h mod))
        (ensures (fun h0 _ h1 -> live h1 r_i /\ live h1 mod /\ modifies2 mod r_i h0 h1))
let bn_remainder_core #rLen #modLen r_i mod count =
  push_frame();
  let mod1 = create modLen (uint 0) in
  let tmp = create rLen (uint 0) in

  let h0 = FStar.HyperStack.ST.get () in
  let inv h _ = live h r_i /\ live h mod /\ live h mod1 /\ live h tmp /\
                modifies4 mod r_i mod1 tmp h0 h in

  trace "bn_remainder_core\n";

  for 0ul count inv (fun i ->
    trace "bn_remainder_core loop start, r_i,mod:\n";
    trace_lbignum r_i;
    trace_lbignum mod;
    if bn_is_geq r_i mod
      then (let _ = bn_sub r_i mod tmp in
      trace "reducing\n";
      copy r_i tmp); // in-place sub?
    bn_rshift1 mod mod1;
    copy mod mod1
  );

  pop_frame()

val calc_bits_test:
     #aLen:bn_len_strict
  -> a:lbignum aLen
  -> ind:size_t{v ind / 64 < v aLen}
  -> Stack size_t
    (requires fun h -> live h a)
    (ensures  fun h0 _ h1 -> modifies0 h0 h1 /\ h0 == h1)
let rec calc_bits_test #aLen a ind =
  if bn_is_bit_set a ind
  then ind +! 1ul
  else if ind =. 0ul then 0ul else calc_bits_test a (ind -! 1ul)

// Returns the index of the highest bit set plus one.
val calc_bits:
     #aLen:bn_len_strict
  -> a:lbignum aLen
  -> Stack size_t
    (requires fun h -> live h a)
    (ensures  fun h0 _ h1 -> modifies0 h0 h1 /\ h0 == h1 /\ live h1 a)
let calc_bits #aLen a = calc_bits_test a (aLen *! 64ul -! 1ul)


/// Copies the part that fits.
val copy_fit:
     #oLen:bn_len
  -> #iLen:bn_len
  -> o:lbignum oLen
  -> i:lbignum iLen
  -> Stack unit
    (requires fun h -> live h o /\ live h i /\ disjoint i o)
    (ensures fun h0 _ h1 -> live h1 o /\ live h1 i /\ modifies1 o h0 h1)
let copy_fit #oLen #iLen o i =
  if iLen =. oLen then
  (trace "copy_fit 1\n"; copy o i)
  else if iLen >. oLen then
  (trace "copy_fit 2\n"; copy o (sub i 0ul oLen))
  else begin
    trace "copy_fit 3\n";
    copy (sub o 0ul iLen) i;
    memset (sub o iLen (oLen -. iLen)) (uint 0) (oLen -. iLen)
  end


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


// Central part of remainder, w/o it remainder verifies for ages.
val bn_remainder_reduce:
     #aLen:bn_len{ v aLen * 64 <= max_size_t }
  -> #modLen:bn_len{ v modLen * 64 <= max_size_t }
  -> a:lbignum aLen
  -> mod:lbignum modLen
  -> res:lbignum modLen
  -> realALen:bn_len{ v realALen <= v aLen }
  -> diffBits:size_t
  -> mod1Len:bn_len{v mod1Len = v modLen + (v diffBits / 64) + 1 /\ v mod1Len >= v realALen}
  -> count:size_t
  -> Stack unit
    (requires fun h ->
     live h a /\ live h mod /\ live h res /\
     disjoint res a /\ disjoint res mod /\ as_snat h mod > 1)
    (ensures fun h0 _ h1 ->
     live h1 a /\ live h1 mod /\ live h1 res /\ modifies1 res h0 h1)
let bn_remainder_reduce #aLen #modLen a mod res realALen diffBits mod1Len count =
    push_frame();

    let mod1 = create mod1Len (uint 0) in
    bn_lshift mod diffBits mod1;

    let mod2 = sub mod1 0ul realALen in

    let res1 = create aLen (uint 0) in
    copy res1 a;

    bn_remainder_core res1 mod2 count;

    copy_fit res res1;
    pop_frame()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 0"

// res = a % n
val bn_remainder:
     #aLen:bn_len{ v aLen * 64 <= max_size_t }
  -> #modLen:bn_len{ v modLen * 64 <= max_size_t }
  -> a:lbignum aLen
  -> mod:lbignum modLen
  -> res:lbignum modLen
  -> Stack unit
    (requires fun h ->
       live h a /\ live h mod /\ live h res /\
       disjoint res a /\ disjoint res mod /\ as_snat h mod > 1)
    (ensures fun h0 _ h1 ->
       live h1 a /\ live h1 mod /\ live h1 res /\ modifies1 res h0 h1 /\
       as_snat h1 res = as_snat h0 a % as_snat h0 mod)
let bn_remainder #aLen #modLen a mod res =
  let h0 = FStar.HyperStack.ST.get () in

  push_frame();

  let modBits = calc_bits mod in
  let aBits = calc_bits a in

  if aBits =. 0ul then begin
    trace "aBits = 0\n";
    memset res (uint 0) modLen
  end else if modBits >. aBits then copy_fit res a
  else begin
    trace "remainder reduction branch\n";
    ne_lemma aBits 0ul;
    assert (v aBits > 0);

    let realALen = blocks aBits 64ul in
    assume (v realALen <= v aLen); // always true

    [@inline_let]
    let maxLen:bn_len_strict = if aLen >=. modLen then aLen else modLen in

    let diffBits = aBits -! modBits in
    assume (v diffBits < 64 * v maxLen); // always true

    let mod1Len:bn_len = begin
        let modk = diffBits /. 64ul in
        assert (v modLen + v modk + 1 <= 3 * v maxLen);
        assert (3 * v maxLen <= max_size_t);
        assert (v modLen + v modk + 1 <= max_size_t);
        modLen +! modk +! 1ul
      end in

    let count:size_t = begin
        assert (v diffBits + 1 <= 64 * v maxLen);
        assert (64 * v maxLen <= max_size_t);
        assert (v diffBits + 1 <= max_size_t);
        (diffBits +! 1ul)
    end in

    // They are equal if modLen < realALen
    assume (v mod1Len >= v realALen);

    bn_remainder_reduce a mod res realALen diffBits mod1Len count
  end;

  pop_frame();

  let h1 = FStar.HyperStack.ST.get () in
  assume (as_snat h1 res = as_snat h0 a % as_snat h0 mod)


#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"


val bn_modular_add:
     #len:bn_len{ (v len + 1) * 64 <= max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       disjoint res a /\ disjoint res b /\ disjoint res n /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
       live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
       modifies (loc res) h0 h1 /\
       as_snat h1 res = (as_snat h0 a + as_snat h0 b) % as_snat h0 n)
let bn_modular_add #len n a b res =
  if enable_ossl then ossl_mod_add #len n a b res else begin
    push_frame();
    let res' = create (len +! 1ul) (uint 0) in
    bn_add_exact a b res';
    bn_remainder res' n res;
    pop_frame()
  end

noextract
val sub_indifferent_zero: a:nat -> b:nat -> n:big -> Lemma
  (requires (a - b) % n = 0)
  (ensures (b - a) % n = 0)
let sub_indifferent_zero a b n =
  to_fe_sub #n a b;
  add_move_to_right #n (to_fe #n a) (to_fe #n b) 0;
  add_sub_zero #n (to_fe #n b);
  add_move_to_left #n (to_fe #n b) (to_fe #n a) 0;
  to_fe_sub #n b a

val bn_modular_sub:
     #len:bn_len{ (v len + 1) * 64 <= max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       disjoint res a /\ disjoint res b /\ disjoint res n /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
       live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
       modifies (loc res) h0 h1 /\
       as_snat h1 res = (as_snat h0 a - as_snat h0 b) % as_snat h0 n)
let rec bn_modular_sub #len n a b res =
  if enable_ossl then ossl_mod_sub #len n a b res else begin
    if bn_is_geq a b then begin
      push_frame();
      let res' = create len (uint 0) in
      let c = bn_sub a b res' in
      assert (v c = 0);
      bn_remainder res' n res;
      pop_frame()
    end else begin
      bn_modular_sub n b a res;
      if not (bn_is_zero res) then begin
        bn_sub_exact n res res;
        let h = FStar.HyperStack.ST.get () in
        assert (as_snat h res = as_snat h n - (as_snat h b - as_snat h a) % as_snat h n);
        to_fe_neg #(as_snat h n) (as_snat h b - as_snat h a);
        assert (as_snat h res = (as_snat h a - as_snat h b) % as_snat h n)
      end else begin
        let h = FStar.HyperStack.ST.get () in
        sub_indifferent_zero (as_snat h b) (as_snat h a) (as_snat h n);
        assert ((as_snat h a - as_snat h b) % as_snat h n = 0)
      end
    end
  end


val bn_modular_mul:
     #len:bn_len_strict{v len * 128 < max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       disjoint res a /\ disjoint res b /\ disjoint res n /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
       live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
       modifies (loc res) h0 h1 /\
       as_snat h1 res = (as_snat h0 a * as_snat h0 b) % as_snat h0 n)
let bn_modular_mul #len n a b res =
  if enable_ossl then ossl_mod_mul n a b res else begin
    push_frame ();
    let res' = create (len +! len) (uint 0) in
    bn_mul a b res';
    bn_remainder res' n res;
    pop_frame ()
  end

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val bn_modular_karatsuba:
     #nLen:bn_len_strict{v nLen * 128 < max_size_t}
  -> pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t}
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> b:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h res /\ live h n /\
      disjoint res a /\ disjoint res b /\ disjoint res n /\
      as_snat h n > 1)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
let bn_modular_karatsuba #nLen pow2_i n a b res =
  if pow2_i <>. nLen
  then (bn_modular_mul n a b res)
  else begin
    push_frame ();
    let res' = bn_zero #(nLen +. nLen +. 4ul *. pow2_i) in
    assume (v (nLen +. nLen +. 4ul *. pow2_i) * 64 < max_size_t);
    karatsuba pow2_i nLen a b res';
    bn_remainder res' n res;
    pop_frame ()
  end


val naive_mod_exp_loop:
     #nLen:bn_len_strict{(v nLen + v nLen) * 64 < max_size_t}
  -> #expLen:bn_len_strict
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> b:lbignum expLen
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
        disjoint n b /\ disjoint n res /\
        live h n /\ live h a /\ live h b /\ live h res /\
        as_snat h n > 1)
    (ensures fun h0 _ h1 -> modifies2 res b h0 h1 /\
        live h1 n /\ live h1 a /\ live h1 b /\ live h1 res)
let rec naive_mod_exp_loop #nLen #expLen n a b res =
  push_frame ();
  let tmp = create expLen (uint 0) in
  let tmp' = create nLen (uint 0) in
  assert_norm (issnat 0);
  assert_norm (nat_bytes_num 0 =. 1ul);
  let zero:lbignum 1ul = nat_to_bignum_exact 0 in
  let isnull = bn_is_equal b zero in
  if not isnull then begin
     let odd = eq_u64 (b.(0ul) &. uint 1) (uint 1) in
     bn_rshift1 b tmp; copy b tmp;
     naive_mod_exp_loop #nLen n a b res;
     bn_modular_mul n res res tmp'; copy res tmp';
     if odd then (bn_modular_mul n res a tmp'; copy res tmp')
  end;
  pop_frame ()

val bn_modular_exp:
     #nLen:bn_len_strict{v nLen * 128 < max_size_t}
  -> #expLen:bn_len_strict
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> b:lbignum expLen
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h n /\ live h a /\ live h b /\ live h res /\
      disjoint a res /\ disjoint b res /\ disjoint n res /\
      as_snat h n > 1)
    (ensures  fun h0 _ h1 -> modifies1 res h0 h1 /\
      live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
      (let n = as_snat h0 n in
       as_snat h1 res = mexp (to_fe #n (as_snat h0 a)) (as_snat h0 b)))
let bn_modular_exp #nLen #expLen n a b res =
  if enable_ossl then ossl_mod_exp n a b res else begin
    let h0 = FStar.HyperStack.ST.get () in

    push_frame ();

    memset res (uint 0) nLen;
    res.(0ul) <- uint 1;
    let tmp_b = create expLen (uint 0) in
    copy tmp_b b;
    naive_mod_exp_loop n a tmp_b res;

    pop_frame ();

    let h1 = FStar.HyperStack.ST.get () in
    assume (let n' = as_snat h0 n in
            as_snat h1 res =
            mexp (to_fe #n' (as_snat h0 a)) (as_snat h0 b))
  end
