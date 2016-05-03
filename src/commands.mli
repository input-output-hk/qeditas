(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Mathdata
open Assets
open Signat
open Ctre

(***
val addnode : string -> int -> bool
***)

val walletkeys : (big_int * bool * (big_int * big_int) * string * hashval * string) list ref
val walletendorsements : (payaddr * payaddr * (big_int * big_int) * int * bool * signat) list ref
val walletwatchaddrs : addr list ref
val stakingassets : (p2pkhaddr * hashval * int64 * obligation * int64) list ref
val storagetrmassets : (hashval option * tm * tp * hashval * hashval) list ref
val storagedocassets : (pubaddr * hashval * hashval option * pdoc * hashval * hashval) list ref
val recenttxs : (hashval,Tx.stx) Hashtbl.t
val txpool : (hashval,Tx.stx) Hashtbl.t

val load_recenttxs : unit -> unit
val load_txpool : unit -> unit
val load_wallet : unit -> unit
val save_wallet : unit -> unit

val printassets : unit -> unit
val printassets_at_ledger : string -> unit

val btctoqedaddr : string -> unit
val importprivkey : string -> unit
val importbtcprivkey : string -> unit
val importendorsement : string -> string -> string -> unit
val importwatchaddr : string -> unit
val importwatchbtcaddr : string -> unit
