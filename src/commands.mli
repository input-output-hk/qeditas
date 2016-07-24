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
val unconfirmed_spent_assets : (hashval,hashval) Hashtbl.t

val add_to_txpool : hashval -> Tx.stx -> unit
val remove_from_txpool : hashval -> unit

val load_recenttxs : unit -> unit
val load_txpool : unit -> unit
val load_wallet : unit -> unit
val save_wallet : unit -> unit

val printassets : unit -> unit
val printassets_in_ledger : hashval -> unit
val printctreeinfo : hashval -> unit
val printctreeelt : hashval -> unit
val printhconselt : hashval -> unit
val printasset : hashval -> unit
val printtx : hashval -> unit

val btctoqedaddr : string -> unit
val importprivkey : string -> unit
val importbtcprivkey : string -> unit
val importendorsement : string -> string -> string -> unit
val importwatchaddr : string -> unit
val importwatchbtcaddr : string -> unit

val createsplitlocktx : hashval -> payaddr -> payaddr -> addr -> hashval -> int -> int64 -> int64 -> unit

val signtx : hashval -> string -> unit
val savetxtopool : int64 -> hashval -> string -> unit
val sendtx : int64 -> hashval -> string -> unit
