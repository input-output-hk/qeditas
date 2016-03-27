(* Copyright (c) 2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

val log : out_channel ref
val openlog : unit -> unit
val closelog : unit -> unit
