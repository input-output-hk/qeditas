(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Signat
open Tx
open Ctre
open Block

exception Hung
val sethungsignalhandler : unit -> unit
val input_byte_nohang : in_channel -> float -> int option

type blocktree = BlocktreeNode of blocktree option * hashval list ref * hashval option * hashval option * hashval option * hashval * targetinfo * int32 * int64 * big_int * int64 * bool option ref * bool ref * (hashval * blocktree) list ref

val genesisblocktreenode : blocktree
val lastcheckpointnode : blocktree ref
val bestnode : blocktree ref
val eq_node : blocktree -> blocktree -> bool
val find_best_validated_block_from : blocktree -> big_int -> big_int
val is_recent_staker : hashval -> blocktree -> int -> bool

val lookup_thytree : hashval option -> Mathdata.ttree option
val lookup_sigtree : hashval option -> Mathdata.stree option

val publish_stx : hashval -> stx -> unit
val publish_block : hashval -> block -> unit

val qednetmain : (unit -> unit) -> (unit -> unit) -> unit
