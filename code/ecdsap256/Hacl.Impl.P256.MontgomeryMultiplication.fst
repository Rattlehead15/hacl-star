module Hacl.Impl.P256.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Spec.P256
open Spec.ECDSA.Lemmas

open Hacl.Impl.P.LowLevel

open Lib.Loops
open Hacl.Spec.P256.MontgomeryMultiplication


#set-options "--z3rlimit 200 --fuel  0 --ifuel 0"


inline_for_extraction noextract
val montgomery_multiplication_round_: #c: curve -> t: widefelem c -> t2: widefelem c -> 
  Stack unit
    (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
    (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ wide_as_nat c h1 t2 < getPower2 c * pow2 64 /\
      wide_as_nat c h1 t2 = getPrime c * (wide_as_nat c h0 t % pow2 64))
  
let montgomery_multiplication_round_ #c t t2 =
  let t1 = mod64 t in 
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
  short_mul_bn (prime_buffer #c) t1 t2
  

val montgomery_multiplication_round: #c: curve -> t: widefelem c -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat c h t < getPrime c * getPrime c /\
    eq_or_disjoint t round)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * (wide_as_nat c h0 t % pow2 64)) / pow2 64)

let montgomery_multiplication_round #c t round =
  push_frame(); 
    let len = getCoordinateLenU64 c in  
    let t2 = create (size 2 *! len) (u64 0) in 
    montgomery_multiplication_round_ #c t t2;
    add_long_without_carry t t2 round;
    shift1 round round; 
  pop_frame()  


#push-options "--z3rlimit 400"

val montgomery_multiplication_round_k0_: #c: curve -> k0: uint64 -> t: widefelem c -> 
  t2: widefelem c -> 
  Stack unit
    (requires fun h -> live h t /\ live h t2 /\ wide_as_nat c h t2 = 0)
    (ensures fun h0 _ h1 -> modifies (loc t2) h0 h1 /\ 
      wide_as_nat c h1 t2 < getPower2 c * pow2 64 /\
      wide_as_nat c h1 t2 = getPrime c * (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64))

let montgomery_multiplication_round_k0_ #c k0 t t2 = 
  push_frame();
    let t1 = mod64 #c t in
    
    let y = create (size 1) (u64 0) in 
    let temp = create (size 1) (u64 0) in 
    
    mul_atomic t1 k0 y temp;
    recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 

    let h = ST.get() in 
    let y_ = index y (size 0) in   
    modulo_addition_lemma (uint_v (Lib.Sequence.index (as_seq h y) 0)) (pow2 64) (uint_v (Lib.Sequence.index (as_seq h temp) 0));
    short_mul_bn #c (prime_buffer #c) y_ t2;
  pop_frame()


val montgomery_multiplication_round_k0: #c: curve -> t: widefelem c -> 
  round: widefelem c -> k0: uint64 ->
  Stack unit 
    (requires fun h -> 
      let order = getPrime c in 
      live h t /\ live h round  /\ wide_as_nat c h t < order * order)
    (ensures fun h0 _ h1 -> 
      modifies (loc round) h0 h1 /\ 
      wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * ((uint_v k0 * (wide_as_nat c h0 t % pow2 64)) % pow2 64)) / pow2 64)

let montgomery_multiplication_round_k0 #c t round k0 = 
  push_frame(); 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    
    let len = getCoordinateLenU64 c in 
    let t2 = create (size 2 *! len) (u64 0) in 

    let h0 = ST.get() in 
    montgomery_multiplication_round_k0_ k0 t t2;
    
    assert_by_tactic (getPrime c * (((wide_as_nat c h0 t % pow2 64) * uint_v k0) % pow2 64) == 
      getPrime c * ((uint_v k0 * (wide_as_nat c h0 t % pow2 64)) % pow2 64)) canon;
    
    add_long_without_carry #c t t2 t2; 
    shift1 #c t2 round;
  pop_frame()



val montgomery_multiplication_one_round_proof_st: 
  #c: curve {(getPrime c + 1) % pow2 64 == 0} ->
  t: nat {t < getPrime c * getPrime c} -> 
  result: nat {result = (t + (t % pow2 64) * getPrime c) / pow2 64} ->
  co: nat {co % getPrime c == t % getPrime c} -> 
  Lemma (
    result % getPrime c == co * modp_inv2 #c (pow2 64) % getPrime c  /\
     result < getPrime c * getPrime c)


val lemma_add_lt: a : int -> b: int -> q: int -> q1: int -> Lemma
  (requires (a < q /\ b < q1))
  (ensures (a + b < q + q1))

let lemma_add_lt a b q q1 = ()


let montgomery_multiplication_one_round_proof_st #c t result co = 
  let prime = getPrime c in 
  mult_one_round #c t co; 
  mul_lemma_1 (t % pow2 64) (pow2 64) prime; 
  
  lemma_mult_lt_sqr prime prime (getPower2 c);
  lemma_mult_lt_left (pow2 64) prime (getPower2 c);
  lemma_add_lt (prime * prime) (pow2 64 * prime) (getPower2 c * getPower2 c) (pow2 64 * getPower2 c);
  assert(prime * prime + pow2 64 * prime < getPower2 c * getPower2 c + pow2 64 * getPower2 c);
  assume (pow2 64 < getPower2 c);
  lemma_mult_lt_right (getPower2 c) (pow2 64) (getPower2 c);
  assert (getPower2 c * getPower2 c + pow2 64 * getPower2 c < 2 * getPower2 c * getPower2 c);
  pow2_plus (getPower c) (getPower c);
  pow2_double_mult (2 * getPower c); 
  assert (getPower2 c * getPower2 c + pow2 64 * getPower2 c < pow2 (2 * getPower c + 1));
  lemma_div_lt_nat (getPower2 c * getPower2 c + pow2 64 * getPower2 c) (2 * getPower c + 1) 64;
  assert ((getPower2 c * getPower2 c + pow2 64 * getPower2 c) / pow2 64 < pow2 (2 * getPower c + 1 - 64));
  assume (getPrime c > pow2 (getPower c - 1));

  pow2_plus (getPower c - 1) (getPower c - 1);
  lemma_mult_lt_sqr (pow2 (getPower c - 1)) (pow2 (getPower c - 1)) (getPrime c);
  pow2_lt_compat (2 * getPower c - 2) (2 * getPower c - 63)



val lemma_mod_inv: #c: curve ->  t: int -> Lemma (t % getPrime c = t * modp_inv2 #c (pow2 0) % getPrime c)

let lemma_mod_inv #c t = 
  let prime = getPrime c in 
  lemma_pow_mod_n_is_fpow prime 1 (prime - 2);
  power_one (prime - 2)


(* 

val montgomery_multiplication_buffer_by_one: #c: curve -> a: felem c -> result: felem c -> 
  Stack unit
    (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h result)) 
    (ensures (fun h0 _ h1 -> 
      let prime = getPrime c in 
      modifies (loc result) h0 h1 /\ 
      as_nat c h1 result  = (as_nat c h0 a * modp_inv2_prime (getPower2 c) prime) % prime /\
      as_nat c h1 result = fromDomain_ #c (as_nat c h0 a)))

*)

val lemma_inv1: a: int -> b: int{a < b} -> Lemma (a < b * b)

let lemma_inv1 a b = ()


val lemma_modp_as_pow: #c: curve -> a: nat -> Lemma
    (modp_inv2 #c a == pow (a % getPrime c) (getPrime c - 2) % getPrime c)

let lemma_modp_as_pow #c a = 
  let prime = getPrime c in 
  lemma_pow_mod_n_is_fpow prime (a % prime) (prime - 2)


val lemma_inv2: #c: curve{(getPrime c + 1) % pow2 64 == 0} 
  -> a0: nat -> a_i: nat {a_i < getPrime c * getPrime c} 
  -> a_i1: nat {a_i1 = (a_i + getPrime c * (a_i % pow2 64)) / pow2 64} 
  -> i: nat {i < uint_v (getCoordinateLenU64 c)} -> 
  Lemma 
    (requires (a_i % getPrime c = a0 * modp_inv2 #c (pow2 (i * 64)) % getPrime c))
    (ensures (a_i1 % getPrime c = a0 * modp_inv2 #c (pow2 ((i + 1) * 64)) % getPrime c))


val lemma_inv3: a: int -> b: int -> c: int -> Lemma (a * b * c == a * (b * c))

let lemma_inv3 a b c = ()


let lemma_inv2 #c a0 a_i a_i1 i = 
  let prime = getPrime c in 
  montgomery_multiplication_one_round_proof_st #c a_i a_i1 (a0 * modp_inv2 #c (pow2 (i * 64)));


  lemma_inv3 a0 (modp_inv2 #c (pow2 (i * 64))) (modp_inv2 #c (pow2 64));
  lemma_mod_mul_distr_r a0 (modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64)) prime;

  calc(==)
  {
    modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64) % prime;
    (==) {lemma_modp_as_pow #c (pow2 (i * 64)); lemma_modp_as_pow #c (pow2 64)}
    (pow (pow2 64 % prime) (prime - 2) % prime) * (pow (pow2 (i * 64) % prime) (prime - 2) % prime) % prime;
    (==) {power_distributivity (pow2 64) (prime - 2) prime}
    (pow (pow2 64) (prime - 2) % prime) * (pow (pow2 (i * 64) % prime) (prime - 2) % prime) % prime;
    (==) {power_distributivity (pow2 (i * 64)) (prime - 2) prime}
    (pow (pow2 64) (prime - 2) % prime) * (pow (pow2 (i * 64)) (prime - 2) % prime) % prime;
    (==) {lemma_mod_mul_distr_l (pow (pow2 64) (prime - 2)) (pow (pow2 (i * 64)) (prime - 2) % prime) prime}
    (pow (pow2 64) (prime - 2)) * (pow (pow2 (i * 64)) (prime - 2) % prime) % prime;
    (==) {lemma_mod_mul_distr_r (pow (pow2 64) (prime - 2)) (pow (pow2 (i * 64)) (prime - 2)) prime}
    (pow (pow2 64) (prime - 2)) * (pow (pow2 (i * 64)) (prime - 2)) % prime;
    (==) {power_distributivity_2 (pow2 64) (pow2 (i * 64)) (prime - 2)}
    (pow (pow2 64 * pow2 (i * 64)) (prime - 2)) % prime;
    (==) {pow2_plus 64 (i * 64)}
    (pow (pow2 ((i + 1) * 64)) (prime - 2)) % prime; 
    (==) {power_distributivity (pow2 ((i + 1) * 64)) (prime - 2) prime}
    (pow (pow2 ((i + 1) * 64) % prime) (prime - 2)) % prime; 
    (==) {lemma_modp_as_pow #c (pow2 ((i + 1) * 64))}
    modp_inv2 #c (pow2 ((i + 1) * 64));}



let montgomery_multiplication_buffer_by_one #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 

  let h0 = ST.get() in 

  copy t_low a; 

  let h1 = ST.get() in 
  
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    let prime = getPrime c in 
    live h t /\ wide_as_nat c h t < prime * prime  /\
    wide_as_nat c h t % prime = wide_as_nat c h1 t * modp_inv2 #c (pow2 (i * 64)) % prime
  in 

  assert(wide_as_nat c h0 t = as_nat c h0 t_low + as_nat c h0 t_high * pow2 (v (getCoordinateLenU64 c) * 64));
  
  lemma_inv1 (wide_as_nat c h1 t) (getPrime c);
  lemma_mod_inv #c (wide_as_nat c h1 t);
  
  for 0ul len inv (fun i ->
    let h0_ = ST.get() in 
    montgomery_multiplication_round #c t t; 
    let h1_ = ST.get() in
    montgomery_multiplication_one_round_proof_st #c (wide_as_nat c h0_ t) (wide_as_nat c h1_ t) (wide_as_nat c h0_ t);
    lemma_inv2 #c (wide_as_nat c h1 t) (wide_as_nat c h0_ t) (wide_as_nat c h1_ t) (v i)
  );

  let h2 = ST.get() in 

  assert (inv h2 (uint_v len));
  assert (wide_as_nat c h2 t % getPrime c =  wide_as_nat c h1 t * modp_inv2 #c (pow2 ((uint_v len) * 64)) % getPrime c);

  
  assume (wide_as_nat c h2 t < 2 * getPrime c);
  
  reduction_prime_2prime_with_carry t result;

  let h3 = ST.get() in 
  
  assume (as_nat c h3 result = wide_as_nat c h1 t * modp_inv2 #c (pow2 ((uint_v len) * 64)) % getPrime c);
  admit();
  
  pop_frame()  



let montgomery_multiplication_buffer #c a b result = 
  assert_norm(prime256 > 3);
  push_frame();
  let len = getCoordinateLenU64 c in 
  
  let round = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  mul a b round;  
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    True in 

  for 0ul len inv (fun i -> montgomery_multiplication_round #c round round);
      
  reduction_prime_2prime_with_carry round result; 
  pop_frame()  


let montgomery_square_buffer #c a result = 
  assert_norm(prime256 > 3);
  push_frame();
    
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;  
    let h1 = ST.get() in 
    mul_lemma_ (as_nat P256 h0 a) (as_nat P256 h0 a) prime256;

  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> montgomery_multiplication_round #c t t);

  reduction_prime_2prime_with_carry t result; 
   
  pop_frame()  

