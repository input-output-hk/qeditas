(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash

exception GettingRemoteData
exception RequestRejected
exception IllformedMsg

val netblkh : int64 ref

type msgtype =
  | Version
  | Verack
  | Addr
  | Inv
  | GetData
  | MNotFound
  | GetSTx
  | GetTx
  | GetTxSignatures
  | GetBlock
  | GetBlockdelta
  | GetBlockdeltah
  | GetHeaders
  | STx
  | Tx
  | TxSignatures
  | Block
  | Headers
  | Blockdelta
  | Blockdeltah
  | GetAddr
  | Mempool
  | Alert
  | Ping
  | Pong
  | Reject
  | GetCTreeElement
  | GetHConsElement
  | GetAsset
  | CTreeElement
  | HConsElement
  | Asset
  | Checkpoint
  | AntiCheckpoint

val int_of_msgtype : msgtype -> int

val openlistener : string -> int -> int -> Unix.file_descr
val connectpeer : string -> int -> Unix.file_descr
val connectpeer_socks4 : int -> string -> int -> Unix.file_descr * in_channel * out_channel

type connstate = {
    conntime : float;
    realaddr : string;
    mutable handshakestep : int;
    mutable peertimeskew : int;
    mutable protvers : int32;
    mutable useragent : string;
    mutable addrfrom : string;
    mutable locked : bool;
    mutable lastmsgtm : float;
    mutable pending : (hashval * (bool * float * float * (msgtype * string -> unit))) list;
    mutable sentinv : (int * hashval) list;
    mutable rinv : (int * hashval) list;
    mutable invreq : (int * hashval) list;
    mutable first_header_height : int64; (*** how much header history is stored at the node ***)
    mutable first_full_height : int64; (*** how much block/ctree history is stored at the node ***)
    mutable last_height : int64; (*** how up to date the node is ***)
  }

val msgtype_handler : (msgtype,in_channel * out_channel * connstate * string -> unit) Hashtbl.t

val netlistenerth : Thread.t option ref
val netseekerth : Thread.t option ref
val netconns : (Thread.t * (Unix.file_descr * in_channel * out_channel * connstate option ref)) list ref
val this_nodes_nonce : int64 ref

val remove_dead_conns : unit -> unit

val netlistener : Unix.file_descr -> unit
val netseeker : unit -> unit

val network_time : unit -> int64 * int

val rec_msg : int64 -> in_channel -> hashval option * hashval * msgtype * string
val send_msg : out_channel -> msgtype -> string -> hashval
val broadcast_requestdata : msgtype -> hashval -> unit
