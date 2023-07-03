module Hacl.AES_128_GCM.M32
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.AES_128.BitSlice
open Hacl.Gf128.PreComp

module ST = FStar.HyperStack.ST


#reset-options "--z3rlimit 1500 --max_fuel 1"

let aes_gcm_ctx_len = 396ul

type aes_gcm_ctx = lbuffer uint64 aes_gcm_ctx_len

val aes128_gcm_compute_iv:
    ctx: aes_gcm_ctx
  -> iv_len: size_t
  -> iv: lbuffer uint8 iv_len ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h iv))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let aes128_gcm_compute_iv ctx iv_len iv =
  push_frame();
  if (iv_len =. size 12) then (
    let tag_iv = create 16ul (u8 0) in
    let tag_mix = create 16ul (u8 0) in
    let aes_ctx = sub ctx (size 0) (size 128) in
    let h0 = ST.get() in
    loop_nospec #h0 (size 12) tag_iv
      (fun i -> tag_iv.(i) <- iv.(i));
    uint_to_bytes_be #U32 (sub tag_iv (size 12) (size 4)) (size 1);
    aes128_set_nonce aes_ctx tag_iv;
    aes128_key_block tag_mix aes_ctx;
    ctx.(394ul) <- uint_from_bytes_le #U64 (sub tag_mix 0ul 8ul);
    ctx.(395ul) <- uint_from_bytes_le #U64 (sub tag_mix 8ul 8ul);
    uint_to_bytes_be #U32 (sub tag_iv (size 12) (size 4)) (size 2);
    aes128_set_nonce aes_ctx tag_iv)
  else (
    let gcm_key = create 16ul (u8 0) in
    let tag_iv = create 16ul (u8 0) in
    let size_iv = create 16ul (u8 0) in
    let tag_mix = create 16ul (u8 0) in
    let aes_ctx = sub ctx (size 0) (size 128) in
    let gcm_ctx = sub ctx (size 128) (size 266) in
    uint_to_bytes_be #U64 (sub gcm_key (size 8) (size 8)) gcm_ctx.(size 8);
    uint_to_bytes_be #U64 (sub gcm_key (size 0) (size 8)) gcm_ctx.(size 9);
    ghash tag_iv iv_len iv gcm_key;
    uint_to_bytes_be #U64 (sub size_iv (size 8) (size 8)) (to_u64 (iv_len *. 8ul));
    let h0 = ST.get() in
    loop_nospec #h0 (size 16) size_iv
      (fun i -> size_iv.(i) <- tag_iv.(i) ^. size_iv.(i));
    ghash tag_iv (size 16) size_iv gcm_key;
    aes128_set_nonce aes_ctx tag_iv;
    aes128_key_block tag_mix aes_ctx;
    ctx.(394ul) <- uint_from_bytes_le #U64 (sub tag_mix 0ul 8ul);
    ctx.(395ul) <- uint_from_bytes_le #U64 (sub tag_mix 8ul 8ul);
    uint_to_bytes_be #U32 (sub tag_iv (size 12) (size 4)) ((uint_from_bytes_be #U32 (sub tag_iv (size 12) (size 4))) +. (size 1));
    aes128_set_nonce aes_ctx tag_iv);
  pop_frame()

val aes128_gcm_init:
    ctx: aes_gcm_ctx
  -> key: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let aes128_gcm_init ctx key =
  push_frame();
  let gcm_key = create 16ul (u8 0) in
  let nonce0 = create 16ul (u8 0) in
  let aes_ctx = sub ctx (size 0) (size 128) in
  let gcm_ctx = sub ctx (size 128) (size 266) in
  admit();
  aes128_init aes_ctx key nonce0;
  aes128_key_block gcm_key aes_ctx;
  gcm_init gcm_ctx gcm_key;
  pop_frame()


val aes128_gcm_encrypt:
    ctx: aes_gcm_ctx
  -> len: size_t{v len + 16 <= max_size_t}
  -> out: lbuffer uint8 (len +. 16ul)
  -> text: lbuffer uint8 len
  -> aad_len: size_t
  -> aad: lbuffer uint8 aad_len ->
  Stack unit
  (requires (fun h -> live h out /\ live h text /\ live h aad /\ live h ctx
                 /\ disjoint out ctx
                 /\ disjoint ctx text
                 /\ disjoint ctx aad
                 /\ disjoint out text
                 /\ disjoint out aad))
  (ensures (fun h0 _ h1 -> modifies2 out ctx h0 h1))

let aes128_gcm_encrypt ctx len out text aad_len aad =
  push_frame();
  let tmp = create 16ul (u8 0) in
  let cip = sub out (size 0) len in
  let aes_ctx = sub ctx (size 0) (size 128) in
  let gcm_ctx = sub ctx (size 128) (size 266) in
  let tag_mix = sub ctx (size 394) (size 2) in
  admit();
  aes128_ctr len cip text aes_ctx;
  gcm_update_blocks_padded gcm_ctx aad_len aad;
  gcm_update_blocks_padded gcm_ctx len cip;
  uint_to_bytes_be #U64 (sub tmp (size 0) (size 8)) (to_u64 (aad_len *. 8ul));
  uint_to_bytes_be #U64 (sub tmp (size 8) (size 8)) (to_u64 (len *. 8ul));
  gcm_update_blocks gcm_ctx (size 16) tmp;
  gcm_emit tmp gcm_ctx;
  let tmp0 = uint_from_bytes_le #U64 (sub tmp 0ul 8ul) in
  let tmp1 = uint_from_bytes_le #U64 (sub tmp 8ul 8ul) in
  let tmp0 = tmp0 ^. tag_mix.(0ul) in
  let tmp1 = tmp1 ^. tag_mix.(1ul) in
  uint_to_bytes_le #U64 (sub out len 8ul) tmp0;
  uint_to_bytes_le #U64 (sub out (len +. 8ul) 8ul) tmp1;
  gcm_ctx.(0ul) <- u64 0;
  gcm_ctx.(1ul) <- u64 0;
  pop_frame()


#reset-options "--z3rlimit 1500 --max_fuel 1"

val aes128_gcm_decrypt:
    ctx: aes_gcm_ctx
  -> len: size_t{v len + 16 <= max_size_t}
  -> out: lbuffer uint8 len
  -> cipher: lbuffer uint8 (len +. 16ul)
  -> aad_len: size_t
  -> aad: lbuffer uint8 aad_len ->
  Stack bool
  (requires (fun h -> live h out /\ live h cipher /\ live h aad /\ live h ctx
                 /\ disjoint out ctx
                 /\ disjoint ctx cipher
                 /\ disjoint ctx aad
                 /\ disjoint out cipher
                 /\ disjoint out aad))
  (ensures (fun h0 r h1 -> modifies2 out ctx h0 h1))

let aes128_gcm_decrypt ctx len out cipher aad_len aad =
  admit();
  push_frame();
  let scratch = create 18ul (u8 0) in
  let text = sub scratch 0ul 16ul in
  let zero = sub scratch 16ul 1ul in
  let result = sub scratch 17ul 1ul in
  let ciphertext = sub cipher 0ul len in
  let tag = sub cipher len (size 16) in
  let aes_ctx = sub ctx (size 0) (size 128) in
  let gcm_ctx = sub ctx (size 128) (size 266) in
  let tag_mix = sub ctx (size 394) (size 2) in
  let h1 = ST.get () in
  gcm_update_blocks_padded gcm_ctx aad_len aad;
  gcm_update_blocks_padded gcm_ctx len ciphertext;
  uint_to_bytes_be #U64 (sub text (size 0) (size 8)) (to_u64 (aad_len *. size 8));
  uint_to_bytes_be #U64 (sub text (size 8) (size 8)) (to_u64 (len *. size 8));
  gcm_update_blocks gcm_ctx (size 16) text;
  gcm_emit text gcm_ctx;
  let text0 = uint_from_bytes_le #U64 (sub text 0ul 8ul) in
  let text1 = uint_from_bytes_le #U64 (sub text 8ul 8ul) in
  let text0 = text0 ^. tag_mix.(0ul) in
  let text1 = text1 ^. tag_mix.(1ul) in
  uint_to_bytes_le #U64 (sub text 0ul 8ul) text0;
  uint_to_bytes_le #U64 (sub text 8ul 8ul) text1;
  let h7 = ST.get () in
  loop_nospec #h7 (size 16) result
    (fun i -> result.(0ul) <- result.(0ul) |. (text.(i) ^. tag.(i)));
  let h8 = ST.get () in
  assert(modifies2 ctx scratch h1 h8);
  let res8 = result.(0ul) in
  let r =
    if Lib.RawIntTypes.u8_to_UInt8 res8 = 0uy then (
      aes128_ctr len out ciphertext aes_ctx;
      true)
    else (
      let h9 = ST.get () in
      //modifies2_is_modifies3 ctx scratch out h1 h9;
      assume(modifies3 out ctx scratch h1 h9);
      false)
  in
  pop_frame();
  r
