(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Sha256

type md = int32 * int32 * int32 * int32 * int32
val ripemd160_md256 : md256 -> md
val hexstring_md : string -> md
val md_hexstring : md -> string
