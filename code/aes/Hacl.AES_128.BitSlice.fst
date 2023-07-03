module Hacl.AES_128.BitSlice

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.AES.Core
open Hacl.Impl.AES.Generic

module ST = FStar.HyperStack.ST

let aes_ctx = aes_ctx M32 Spec.AES.AES128
let skey = skey Spec.AES.AES128

[@ CInline ]
val create_ctx: unit ->
  StackInline aes_ctx
  (requires (fun h -> True))
  (ensures  (fun h0 f h1 -> live h1 f))

[@ CInline ]
let create_ctx () = create_ctx M32 Spec.AES.AES128


[@ CInline ]
val aes128_init:
    ctx: aes_ctx
  -> key: skey
  -> nonce: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1))

[@ CInline ]
let aes128_init ctx key nonce = aes128_bitslice_init ctx key nonce


[@ CInline ]
val aes128_set_nonce:
    ctx: aes_ctx
  -> nonce: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 ctx h0 h1))

[@ CInline ]
let aes128_set_nonce ctx nonce = aes_set_nonce ctx nonce


[@ CInline ]
val aes128_key_block:
    kb: lbuffer uint8 16ul
  -> ctx:aes_ctx ->
  Stack unit
  (requires (fun h -> live h kb /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 kb h0 h1))

[@ CInline ]
let aes128_key_block kb ctx = aes_key_block #M32 #Spec.AES.AES128 kb ctx


inline_for_extraction noextract
val aes128_update4:
    out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx
  -> counter: size_t ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1))

let aes128_update4 out inp ctx ctr = aes_update4 out inp ctx ctr

inline_for_extraction noextract
val aes128_ctr:
  len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes128_ctr len out inp ctx = aes_ctr #M32 #Spec.AES.AES128 len out inp ctx


[@ CInline ]
val aes128_ctr_encrypt:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey
  -> n:lbuffer uint8 16ul
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes128_ctr_encrypt len out inp k n = aes_ctr_encrypt #M32 #Spec.AES.AES128 len out inp k n


[@ CInline ]
val aes128_ctr_decrypt:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey
  -> n:lbuffer uint8 16ul
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let aes128_ctr_decrypt len out inp k n = aes_ctr_decrypt #M32 #Spec.AES.AES128 len out inp k n
