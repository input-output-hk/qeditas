(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Mathdata
open Assets
open Signat

(***
val addnode : string -> int -> bool
***)

val walletkeys : (big_int * bool * (big_int * big_int) * string * hashval * string) list ref
val walletendorsements : (payaddr * payaddr * int * signat) list ref
val walletwatchaddrs : addr list ref
val stakingassets : (p2pkhaddr * hashval * int64 * obligation * int64) list ref
val storagetrmassets : (hashval option * tm * tp * hashval * hashval) list ref
val storagedocassets : (pubaddr * hashval * hashval option * pdoc * hashval * hashval) list ref

val read_wallet : unit -> unit
val write_wallet : unit -> unit

val printassets : unit -> unit

val importprivkey : string -> unit
val importbtcprivkey : string -> unit
(***
val importwatchaddr : string -> unit
val importwatchbtcaddr : string -> unit
***)
