module Hacl.Tube.Receive


open FStar.Seq
open FStar.Buffer
open FileIO.Types
open PaddedFileIO
open SocketIO
open Hacl.Constants
open Hacl.Cast
open Box.Ideal
open Hacl.Tube.Send

#reset-options "--initial_fuel 0 --max_fuel 0"


module  U8=FStar.UInt8
module U32=FStar.UInt32
module U64=FStar.UInt64

module  H8=Hacl.UInt8
module H32=Hacl.UInt32
module H64=Hacl.UInt64

private val lemma_max_uint8: n:nat -> Lemma
 (requires (n = 8))
 (ensures  (pow2 n = 256))
 [SMTPat (pow2 n)]
let lemma_max_uint8 n = assert_norm(pow2 8 = 256)
private val lemma_max_uint32: n:nat -> Lemma
 (requires (n = 32))
 (ensures  (pow2 n = 4294967296))
 [SMTPat (pow2 n)]
let lemma_max_uint32 n = assert_norm(pow2 32 = 4294967296)
private val lemma_max_uint64: n:nat -> Lemma
 (requires (n = 64))
 (ensures  (pow2 n = 18446744073709551616))
 [SMTPat (pow2 n)]
let lemma_max_uint64 n = assert_norm(pow2 64 = 18446744073709551616)


#reset-options "--initial_fuel 0 --max_fuel 0"

(** Non-Constant time comparison function **)
val memcmp:
  b:buffer u8 ->
  b':buffer u8 ->
  len:U32.t{U32.v len <= length b /\ U32.v len <= length b'} ->
  Stack U8.t
    (requires (fun h -> live h b /\ live h b'))
    (ensures  (fun h0 r h1 -> h0 == h1))
let rec memcmp b b' len =
  if U32 (len =^ 0ul) then (
    0xffuy
  ) else (
    let i = U32 (len -^ 1ul) in
    if U8 (b.(i) =^ b'.(i)) then
       memcmp b b' i
    else 0x00uy)


val get_fh_stat: file_handle -> Tot file_stat
let get_fh_stat fh = fh.stat


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

val file_recv_loop_2:
  fb:fh_ref ->
  connb:socket_ref ->
  state: uint8_p{length state = 1244} ->
  mut_state:uint8_p{length mut_state = U64.v ciphersize + 24 /\ frameOf mut_state <> frameOf state} ->
  seqno:H64.t ->
  len:U64.t ->
  Stack sresult
    (requires (fun h ->
      live h connb
      /\ current_state h (get h connb 0) = Open
      /\ live_file h fb
      /\ (let fh = get h fb 0 in file_state h fh = FileOpen)
      /\ live h state /\ live h mut_state))
    (ensures  (fun h0 r h1 ->
      live_file h1 fb /\ file_state h1 (get h1 fb 0) = FileOpen /\ live h1 connb
      /\ same_file h0 fb h1 fb
      /\ (match r with
      | SocketOk -> (current_state h1 (get h1 connb 0) = Open)
      | _ -> true) ))
let rec file_recv_loop_2 fb connb state mut_state seqno len =
  let key        = Buffer.sub state 64ul 32ul in
  let ciphertext = Buffer.sub mut_state 0ul (ciphersize_32) in
  let nonce      = Buffer.sub mut_state ciphersize_32 24ul in
  if U64 (len =^ 0uL) then SocketOk
  else
  if U64 (len <^ blocksize) then (
    let h0 = ST.get() in
    match tcp_read_all connb ciphertext (cipherlen len) with
    | SocketOk -> (
        let h1 = ST.get() in
        lemma_reveal_modifies_1 mut_state h0 h1;
        let next = file_next_write_buffer fb blocksize in
        let h2 = ST.get() in
        store64_le (sub nonce 16ul 8ul) seqno;
        let h3 = ST.get() in
        lemma_reveal_modifies_1 mut_state h2 h3;
        let seqno = H64 (seqno +%^ one_64) in
        Math.Lemmas.modulo_lemma (U64.v len) (pow2 32);
        let ciphertext' = Buffer.sub ciphertext 0ul (cipherlen_32 (Int.Cast.uint64_to_uint32 len)) in
        let next' = Buffer.sub next 0ul (Int.Cast.uint64_to_uint32 len) in
        if U32 (Hacl.Box.crypto_box_open_easy_afternm next' ciphertext' (cipherlen len) nonce key =^ 0ul) then (
          let h4 = ST.get() in
          lemma_reveal_modifies_1 next h3 h4;
	  SocketOk )
	else  (TestLib.perr(20ul); SocketError))
    | SocketError -> TestLib.perr(21ul); TestLib.perr(Int.Cast.uint64_to_uint32 len); SocketError)
  else (
    let h0 = ST.get() in
    match tcp_read_all connb ciphertext ciphersize with
    | SocketOk -> (
        let h1 = ST.get() in
        lemma_reveal_modifies_1 mut_state h0 h1;
        let rem = U64 (len -^ blocksize) in
        let next = file_next_write_buffer fb blocksize in
        let h1 = ST.get() in
        store64_le (sub nonce 16ul 8ul) seqno;
        let seqno = H64 (seqno +%^ one_64) in
        let h = ST.get() in
        lemma_reveal_modifies_1 mut_state h1 h;
        if U32 (Hacl.Box.crypto_box_open_easy_afternm next ciphertext ciphersize nonce key =^ 0ul) then (
          let h2 = ST.get() in
          lemma_reveal_modifies_1 next h h2;
          assume (live_file h2 fb /\ (let fh = get h2 fb 0 in file_state h2 fh = FileOpen));
          file_recv_loop_2 fb connb state mut_state seqno rem )
        else (TestLib.perr(20ul); SocketError) )
    | SocketError -> TestLib.perr(21ul); TestLib.perr(Int.Cast.uint64_to_uint32 len); SocketError
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 200"

val file_recv_enc:
  fb:fh_ref ->
  connb:socket_ref ->
  state: uint8_p{length state = 1244} ->
  hsize: U64.t ->
  Stack sresult
    (requires (fun h -> live h connb /\ current_state h (get h connb 0) = Open
      /\ live_file h fb (* /\ (let fh = get h fb 0 in file_state h fh = FileOpen) *)
      /\ live h state))
    (ensures  (fun h0 r h1 -> match r with
      | SocketOk -> (live h1 fb (* /\ live h1 lb /\ current_state h1 (get h1 lb 0) = Open *)
      /\ live h1 connb /\ live h1 state)
      | _ -> true))

let file_recv_enc fb connb state size =
  push_frame();
  let sid   = Buffer.sub state 96ul 16ul in
  let header  = Buffer.sub state 220ul 1024ul in
  let seqno = 0uL in
  let h0 = ST.get() in
  let mut_state = Buffer.create zero_8 (U32 (ciphersize_32 +^ 24ul)) in
  let ciphertext = Buffer.sub mut_state 0ul (ciphersize_32) in
  let nonce      = Buffer.sub mut_state ciphersize_32 24ul in
  let key   = Buffer.sub state 64ul 32ul in
  let pkA   = Buffer.sub state 0ul 32ul in
  let pkB   = Buffer.sub state 32ul 32ul in
  let h1 = ST.get() in
  lemma_reveal_modifies_0 h0 h1;
  let res =
    (match tcp_read_all connb ciphertext (cipherlen(headersize)) with
      | SocketOk -> (
          let h0 = ST.get() in
          blit sid 0ul nonce 0ul 16ul;
          store64_le (sub nonce 16ul 8ul) seqno;
          let seqno = H64 (seqno +^ 1uL) in
          let h = ST.get() in
          assume (as_seq h key == agreedKey (as_seq h pkA) (as_seq h pkB));
          let ciphertext' = Buffer.sub ciphertext 0ul (U32 (headersize_32 +^ 16ul)) in
          if U32 (crypto_box_open_easy_afternm #pkA #pkB header ciphertext' (cipherlen(headersize)) nonce key =^ 0ul) then (
	     let h1 = ST.get() in
             lemma_reveal_modifies_2 state mut_state h0 h1;
             let file_size = load64_le (sub header 0ul  8ul) in
             let nsize     = load64_le (sub header 8ul  8ul) in
             let mtime     = load64_le (sub header 16ul 8ul) in
             assume(H64.v nsize < 100);
             assume(H64.v file_size < pow2 32);
             Math.Lemmas.modulo_lemma (U64.v nsize) (pow2 32);
             let file = sub header 24ul (Int.Cast.uint64_to_uint32 nsize) in
             let fstat = {name = file; mtime = mtime; size = file_size} in
             (match file_open_write_sequential fstat fb with
              | FileOk -> 
                  (match file_recv_loop_2 fb connb state mut_state seqno size with
                   | SocketOk -> (
     		         match file_close fb with
                       | false -> (
                             match tcp_close connb with
                            | SocketOk -> (
                                  SocketOk )
                            | SocketError -> TestLib.perr(13ul); SocketError )
                       | true -> TestLib.perr(12ul); SocketError )
                  | SocketError -> TestLib.perr(10ul); SocketError )
              | FileError -> TestLib.perr(9ul); SocketError )
          ) else (
             TestLib.perr(8ul); SocketError ) )
      | SocketError -> SocketError ) in
  pop_frame();
  res

                 
#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 500"

val file_recv_loop:
  fb:fh_ref ->
  lb:socket_ref ->
  connb:socket_ref{disjoint lb connb} ->
  state: uint8_p{length state = 1244} ->
  Stack sresult
    (requires (fun h -> live h fb /\ live h lb /\ current_state h (get h lb 0) = Open
      /\ live h connb /\ live h state))
    (ensures  (fun h0 _ h1 -> True))
let rec file_recv_loop fb lhb connb state =
  push_frame();
  let sid   = Buffer.sub state 96ul 16ul in
  let hsbuf   = Buffer.sub state 112ul 8ul in
  let fname   = Buffer.sub state 120ul 100ul in
  let header  = Buffer.sub state 220ul 1024ul in
  let pkA   = Buffer.sub state 0ul 32ul in
  let pkB   = Buffer.sub state 32ul 32ul in
  let h0 = ST.get() in
  let pks = Buffer.create zero_8 64ul in
  let pk1 = Buffer.sub pks 0ul 32ul in
  let pk2 = Buffer.sub pks 32ul 32ul in
  let h1 = ST.get() in
  lemma_reveal_modifies_0 h0 h1;
  let res =
  match tcp_accept lhb connb with
  | SocketOk -> (
      let h2 = ST.get() in
      cut(live h2 fb);
      (* let c1 = C.clock() in *)
      (match tcp_read_all connb sid 16uL with
      | SocketOk -> (
          match tcp_read_all connb hsbuf 8uL with
          | SocketOk -> (
	      let hsize = load64_le hsbuf in
              match tcp_read_all connb pk1 32uL with
              | SocketOk -> (
                  match tcp_read_all connb pk2 32uL with
                  | SocketOk -> (
                      if U8 (memcmp pk1 pkA 32ul =^ 0xffuy) then (
                         if U8 (memcmp pk2 pkB 32ul =^ 0xffuy) then (
                           let h3 = ST.get() in
                           lemma_reveal_modifies_2 state pks h2 h3;
                           assume (live_file h3 fb);
                           cut (live h3 state);
			   let _ = file_recv_enc fb connb state hsize in
			   (* let c2 = C.clock() in *)
			   (* TestLib.print_clock_diff c1 c2; *)
			   SocketOk)
			 else (TestLib.perr(7ul); SocketError) )
                      else (TestLib.perr(6ul); SocketError) )
                  | SocketError -> TestLib.perr(5ul); SocketError )
              | SocketError -> TestLib.perr(4ul); SocketError )
          | SocketError -> TestLib.perr(3ul); SocketError )
      | SocketError -> TestLib.perr(2ul); SocketError ))
  | SocketError -> TestLib.perr(1ul); SocketError in
  pop_frame();
  match res with
  | SocketOk -> file_recv_loop  fb lhb connb state
  | SocketError -> TestLib.perr(0ul); SocketError

val file_recv:
  port:u32 -> 
  pkA:publicKey{frameOf pkA <> file_rgn /\ frameOf pkA <> socket_rgn} -> 
  skB:privateKey {frameOf skB <> file_rgn /\ frameOf skB <> socket_rgn /\ disjoint pkA skB} -> 
  ST open_result
    (requires (fun h -> live h pkA /\ live h skB))
    (ensures  (fun h0 s h1 -> match s.r with
       	                   | FileOk -> true				     
		           | _ -> true))
let file_recv p pkA skB =
  push_frame();
  (* Initialization of the file_handle *)
  let fb = Buffer.rcreate file_rgn (init_file_handle(TestLib.uint8_p_null)) 1ul in
  let fh = fb.(0ul) in
  let state = Buffer.create zero_8 1244ul  in
  let pkA_cpy  = Buffer.sub state 0ul 32ul in
  let pkB   = Buffer.sub state 32ul 32ul in
  let key   = Buffer.sub state 64ul 32ul in
  let sid   = Buffer.sub state 96ul 16ul in
  let hsbuf   = Buffer.sub state 112ul 8ul in
  let fname   = Buffer.sub state 120ul 100ul in
  let header  = Buffer.sub state 220ul 1024ul in
  blit pkA 0ul pkA_cpy 0ul 32ul;
  getPublicKey skB pkB;
  let keygen_res = U32 (crypto_box_beforenm key pkA skB =^ 0ul) in

  (* Initialization of the two sockets *)
  let s = init_socket() in
  let lb = Buffer.rcreate socket_rgn s 1ul in
  let sb = Buffer.rcreate socket_rgn s 1ul in
  let res = (match tcp_listen p lb with
  | SocketOk -> (
      match file_recv_loop fb lb sb state with
      | SocketOk -> opened FileOk fh.stat sid
      | SocketError -> opened FileError fh.stat sid )
  | SocketError -> opened FileError fh.stat sid ) in
  pop_frame();
  res
