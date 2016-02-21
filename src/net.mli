(* Copyright (c) 2015-2016 The Qeditas developers *)
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

type validationstatus = Waiting of float | Valid | Invalid

type blocktree = BlocktreeNode of blocktree option * hashval list ref * hashval option * hashval option * hashval option * hashval * targetinfo * targetinfo * int32 * int64 * big_int * int64 * validationstatus ref * bool ref * (hashval * blocktree) list ref

val genesisblocktreenode : blocktree ref
val lastcheckpointnode : blocktree ref
val bestnode : blocktree ref
val initblocktree : unit -> unit
val node_prevblockhash : blocktree -> hashval option
val eq_node : blocktree -> blocktree -> bool
val find_best_validated_block_from : blocktree -> big_int -> big_int
val is_recent_staker : hashval -> blocktree -> int -> bool

val print_best_node : unit -> unit

val lookup_thytree : hashval option -> Mathdata.ttree option
val lookup_sigtree : hashval option -> Mathdata.stree option

val publish_stx : hashval -> stx -> unit
val publish_block : hashval -> block -> unit

val qednetmain : (unit -> unit) -> (unit -> unit) -> unit
