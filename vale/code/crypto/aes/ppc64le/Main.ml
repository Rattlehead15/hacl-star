let parse_cmdline :
  (string * (unit -> (Vale_PPC64LE_Decls.ins,Vale_PPC64LE_Decls.ocmp) Vale_PPC64LE_Machine_s.precode) * int * bool) list -> unit
  =
  fun l  ->
  let printer = Vale_PPC64LE_Decls.gcc in
  (* Extract and print assembly code *)
  Vale_PPC64LE_Decls.print_header printer;
  let _ = List.fold_left (fun label_count (name, code, _, _) ->
                          Vale_PPC64LE_Decls.print_proc name
                                                      (code ())
                                                      label_count printer)
                          (Prims.parse_int "0") l in
  Vale_PPC64LE_Decls.print_footer printer

let _ =
  parse_cmdline [
    ("aes128_key_expansion", (fun () -> Vale_AES_PPC64LE_AES.va_code_KeyExpansionStdcall Vale_AES_AES_BE_s.AES_128), 2, false);
    ("aes128_keyhash_init", (fun () -> Vale_AES_PPC64LE_GF128_Init.va_code_Keyhash_init Vale_AES_AES_BE_s.AES_128), 2, false);
    ("aes256_key_expansion", (fun () -> Vale_AES_PPC64LE_AES.va_code_KeyExpansionStdcall Vale_AES_AES_BE_s.AES_256), 2, false);
    ("aes256_keyhash_init", (fun () -> Vale_AES_PPC64LE_GF128_Init.va_code_Keyhash_init Vale_AES_AES_BE_s.AES_256), 2, false);
    ("compute_iv_stdcall", Vale_AES_PPC64LE_GCMencrypt.va_code_Compute_iv_stdcall, 6, false);
    ("gcm128_encrypt", (fun () -> Vale_AES_PPC64LE_GCMencrypt.va_code_Gcm_blocks_stdcall Vale_AES_AES_BE_s.AES_128), 1, false);
    ("gcm256_encrypt", (fun () -> Vale_AES_PPC64LE_GCMencrypt.va_code_Gcm_blocks_stdcall Vale_AES_AES_BE_s.AES_256), 1, false);
    ("gcm128_decrypt", (fun () -> Vale_AES_PPC64LE_GCMdecrypt.va_code_Gcm_blocks_decrypt_stdcall Vale_AES_AES_BE_s.AES_128), 1, false);
    ("gcm256_decrypt", (fun () -> Vale_AES_PPC64LE_GCMdecrypt.va_code_Gcm_blocks_decrypt_stdcall Vale_AES_AES_BE_s.AES_256), 1, false);
  ]
