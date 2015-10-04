(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2014 Chad E Brown *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* Most of this code is taken directly from Egal. *)

open Big_int
open Secp256k1
open Hash

exception Invalid

val base58 : big_int -> string
val frombase58 : string -> big_int
val qedwif : big_int -> bool -> string
val privkey_from_wif : string -> big_int * bool
val pubkey_hashval : big_int * big_int -> bool -> hashval
val hashval_from_addrstr : string -> hashval
val hashval_btcaddrstr : hashval -> string
val addr_qedaddrstr : addr -> string
val qedaddrstr_addr : string -> addr

