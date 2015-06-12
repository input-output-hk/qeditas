(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Secp256k1
open Signat

val verify_p2sh : big_int -> hashval -> int list -> bool

type gensignat =
  | P2pkhSignat of pt * bool * signat
  | P2shSignat of int list
  | EndP2pkhToP2pkhSignat of pt * bool * pt * bool * signat * signat
  | EndP2pkhToP2shSignat of pt * bool * hashval * signat * int list
  | EndP2shToP2pkhSignat of pt * bool * int list * signat
  | EndP2shToP2shSignat of hashval * int list * int list

val verify_gensignat : big_int -> gensignat -> addr -> bool
