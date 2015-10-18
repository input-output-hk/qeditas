(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Signat
open Tx
open Ctre
open Block

val myaddr : unit -> string

val recentledgerroots : (hashval, int64 * hashval) Hashtbl.t
val recentblockheaders : (hashval * (big_int * int64 * blockheader)) list ref
val recentcommitments : (int64 * hashval) list ref
val recentblockdeltahs : (hashval, blockdeltah) Hashtbl.t
val recentblockdeltas : (hashval, blockdelta) Hashtbl.t
val recentstxs : (hashval, stx) Hashtbl.t

val waitingblock : (int64 * int64 * hashval * blockheader * blockdelta * big_int) option ref

val insertnewblockheader : hashval -> big_int -> bool -> int64 -> blockheader -> unit

exception Hung
exception RequestRejected
exception IllformedMsg

val extract_ip_and_port : string -> string * int * bool

val sethungsignalhandler : unit -> unit
val accept_nohang : Unix.file_descr -> float -> (Unix.file_descr * Unix.sockaddr) option
val input_byte_nohang : in_channel -> float -> int option

val openlistener : string -> int -> int -> Unix.file_descr
val connectpeer : string -> int -> Unix.file_descr
val connectpeer_socks4 : int -> string -> int -> Unix.file_descr * in_channel * out_channel

type msg =
  | Version of int32 * int64 * int64 * string * string * int64 * string * rframe * rframe * rframe * int64 * int64 * int64 * bool * (int64 * hashval) option
  | Verack
  | Addr of (int64 * string) list
  | Inv of (int * int64 * hashval) list (*** for blocks (headers, deltahs, deltas) and ctrees, include the corrsponding block height (int64) ***)
  | GetData of (int * hashval) list
  | MNotFound of (int * hashval) list
  | GetBlocks of int32 * int64 * hashval option
  | GetBlockdeltas of int32 * int64 * hashval option
  | GetBlockdeltahs of int32 * int64 * hashval option
  | GetHeaders of int32 * int64 * hashval option
  | MTx of int32 * stx (*** signed tx in principle, but in practice some or all signatures may be missing ***)
  | MBlock of int32 * block
  | Headers of (int64 * blockheader) list
  | MBlockdelta of int32 * hashval * blockdelta (*** the hashval is for the block header ***)
  | MBlockdeltah of int32 * hashval * blockdeltah (*** the hashval is for the block header; the blockdeltah only has the hashes of stxs in the block ***)
  | GetAddr
  | Mempool
  | Alert of string * signat
  | Ping
  | Pong
  | Reject of string * int * string * string
  | GetFramedCTree of int32 * int64 option * hashval * rframe
  | MCTree of int32 * ctree
  | Checkpoint of int64 * hashval
  | AntiCheckpoint of int64 * hashval

type pendingcallback = PendingCallback of (msg -> pendingcallback option)

type connstate = {
    mutable alive : bool;
    mutable lastmsgtm : float;
    mutable pending : (hashval * bool * float * float * pendingcallback option) list;
    mutable sentinv : (int * hashval) list;
    mutable rinv : (int * hashval) list;
    mutable invreq : (int * hashval) list;
    mutable rframe0 : rframe; (*** which parts of the ctree the node is keeping ***)
    mutable rframe1 : rframe; (*** what parts of the ctree are stored by a node one hop away ***)
    mutable rframe2 : rframe; (*** what parts of the ctree are stored by a node two hops away ***)
    mutable first_header_height : int64; (*** how much header history is stored at the node ***)
    mutable first_full_height : int64; (*** how much block/ctree history is stored at the node ***)
    mutable last_height : int64; (*** how up to date the node is ***)
  }

val conns : (Unix.file_descr * in_channel * out_channel * string * connstate) list ref
val preconns : (Unix.file_descr * in_channel * out_channel * float * int ref * string option ref * connstate option ref) list ref
val this_nodes_nonce : int64 ref

exception EnoughConnections

val getfallbacknodes : unit -> string list

val initialize_conn_accept : Unix.file_descr -> unit
val tryconnectpeer : string -> unit
val addknownpeer : int64 -> string -> unit
val getknownpeers : unit -> string list
val loadknownpeers : unit -> unit
val saveknownpeers : unit -> unit

val broadcast_inv : (int * int64 * hashval) list -> unit
val send_msg : out_channel -> msg -> hashval
val send_reply : out_channel -> hashval -> msg -> hashval

val send_initial_inv : out_channel -> connstate -> unit

val rec_msg_nohang : in_channel -> float -> float -> (hashval option * hashval * msg) option

val handle_msg : in_channel -> out_channel -> connstate -> hashval option -> hashval -> msg -> unit

val try_requests : (int * hashval) list -> unit
