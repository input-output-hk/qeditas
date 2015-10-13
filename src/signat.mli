(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Sha256
open Hash
open Secp256k1

exception ZeroValue

type signat = big_int * big_int

val decode_signature_a : string -> int * bool * signat
val decode_signature : string -> int * signat
val signat_big_int : big_int -> big_int -> big_int -> signat
val signat_hashval : hashval -> big_int -> big_int -> signat
val recover_key : big_int -> signat -> int -> pt

val verify_signed_big_int : big_int -> pt -> signat -> bool
val verify_signed_hashval : hashval -> pt -> signat -> bool
val verify_p2pkhaddr_signat : big_int -> p2pkhaddr -> signat -> int -> bool -> bool

val verifymessage_a : hashval -> int -> bool -> signat -> string -> bool
val verifymessage : hashval -> int -> signat -> string -> bool
val verifybitcoinmessage_a : hashval -> int -> bool -> signat -> string -> bool
val verifybitcoinmessage : hashval -> int -> signat -> string -> bool
val verifymessage_base64 : hashval -> string -> string -> bool
val verifybitcoinmessage_base64 : hashval -> string -> string -> bool

val md256_of_bitcoin_message : string -> md256

val seo_signat : (int -> int -> 'a -> 'a) -> signat -> 'a -> 'a
val sei_signat : (int -> 'a -> int * 'a) -> 'a -> signat * 'a
