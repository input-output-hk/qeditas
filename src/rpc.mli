(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Signat

type rpccom =
    Stop
  | AddNode of string
  | GetInfo
  | ImportWatchAddr of string
  | ImportPrivKey of string

val send_string : out_channel -> string -> unit
val rec_string : in_channel -> string

val send_rpccom : out_channel -> rpccom -> unit
val rec_rpccom : in_channel -> rpccom
val do_rpccom : rpccom -> out_channel -> unit

(***
val addnode : string -> int -> bool
***)

val walletkeys : (big_int * bool * (big_int * big_int) * string * hashval * string) list ref
val walletendorsements : (payaddr * payaddr * signat) list ref
val walletwatchaddrs : addr list ref

val read_wallet : unit -> unit
val write_wallet : unit -> unit
