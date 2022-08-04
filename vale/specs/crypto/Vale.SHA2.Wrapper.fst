module Vale.SHA2.Wrapper

open FStar.UInt32
open Spec.Agile.Hash
open Spec.SHA2
friend Lib.IntTypes
friend Spec.SHA2

let sigma256_0_0 x = v (_sigma0 SHA2_256 (uint_to_t x))

let sigma256_0_1 x = v (_sigma1 SHA2_256 (uint_to_t x))

let sigma256_1_0 x = v (_Sigma0 SHA2_256 (uint_to_t x))

let sigma256_1_1 x = v (_Sigma1 SHA2_256 (uint_to_t x))
