(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int

val hexsubstring_int8 : string -> int -> int
val hexsubstring_int32 : string -> int -> int32
val int8_hexstring : Buffer.t -> int -> unit
val int32_hexstring : Buffer.t -> int32 -> unit
val big_int_sub_int32 : big_int -> int -> int32
val int32_big_int_bits : int32 -> int -> big_int
val int32_rev : int32 -> int32
