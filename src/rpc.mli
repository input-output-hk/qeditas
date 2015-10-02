(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

type rpccom =
    Stop
  | AddNode of string

val send_rpccom : out_channel -> rpccom -> unit
val rec_rpccom : in_channel -> rpccom
val do_rpccom : rpccom -> out_channel -> unit

(***
val addnode : string -> int -> bool
***)
