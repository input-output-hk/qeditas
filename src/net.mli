(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Signat
open Tx
open Ctre
open Block

exception RequestRejected

val extract_ip_and_port : string -> string * int * bool

val sethungsignalhandler : unit -> unit
val accept_nohang : Unix.file_descr -> float -> (Unix.file_descr * Unix.sockaddr) option
val input_byte_nohang : in_channel -> float -> int option

val openlistener : string -> int -> int -> Unix.file_descr
val connectpeer : string -> int -> Unix.file_descr
val connectpeer_socks4 : int -> string -> int -> Unix.file_descr * in_channel * out_channel

type msg =
  | Version of int32 * int64 * int64 * string * string * int64 * string * int64 * bool
  | Verack
  | Addr of int * (int64 * string) list
  | Inv of int * (int * hashval) list
  | GetData of int * (int * hashval) list
  | MNotFound of int * (int * hashval) list
  | GetBlocks of int32 * int * hashval list * hashval option
  | GetHeaders of int32 * int * hashval list * hashval option
  | MTx of int32 * stx (*** signed tx in principle, but in practice some or all signatures may be missing ***)
  | MBlock of int32 * hashval * blockdeltah (*** the hashval is for the block header and blockdeltah only has the hashes of stxs in the block; the header and txs themselves can/should/must be requested separately ***)
  | Headers of int * blockheader list
  | GetAddr
  | Mempool
  | Alert of string * signat
  | Ping
  | Pong
  | Reject of string * int * string * string
  | MCTree of int32 * ctree
  | MNehList of int32 * nehlist
  | MHList of int32 * hlist
  | GetFramedCTree of int32 * hashval * frame

val send_string : out_channel -> string -> unit
val rec_string : in_channel -> string
val send_msg : out_channel -> msg -> unit
val rec_msg_nohang : in_channel -> float -> msg option
val rec_msgs_nohang : in_channel -> float -> msg list

val handle_msg : in_channel -> out_channel -> int64 option ref -> msg -> unit

