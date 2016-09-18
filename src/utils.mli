(* Copyright (c) 2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

val log : out_channel ref
val openlog : unit -> unit
val closelog : unit -> unit

val era : int64 -> int
val maxblockdeltasize : int64 -> int

val random_initialized : bool ref
val initialize_random_seed : unit -> unit
val rand_bit : unit -> bool
val rand_int32 : unit -> int32
val rand_int64 : unit -> int64
