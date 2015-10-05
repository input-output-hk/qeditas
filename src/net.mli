(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

exception RequestRejected

val extract_ipv4 : string -> int * int * int * int
val extract_ip_and_port : string -> string * int

val sethungsignalhandler : unit -> unit
val accept_nohang : Unix.file_descr -> float -> (Unix.file_descr * Unix.sockaddr) option
val input_byte_nohang : in_channel -> float -> int option

val openlocallistener : int -> int -> Unix.file_descr
val openlistener : string -> int -> int -> Unix.file_descr
val connectlocal : int -> Unix.file_descr * in_channel * out_channel
val connectpeer : string -> int -> Unix.file_descr * in_channel * out_channel
val connectpeer_socks4 : int -> string -> int -> Unix.file_descr * in_channel * out_channel
