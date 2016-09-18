(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int

type md256 = int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32

val sha256init : unit -> unit
val currblock : int32 array
val sha256round : unit -> unit
val getcurrmd256 : unit -> md256

val sha256str : string -> md256
val sha256dstr : string -> md256

val md256_hexstring : md256 -> string
val hexstring_md256 : string -> md256

val md256_big_int : md256 -> big_int
val big_int_md256 : big_int -> md256

val seo_md256 : (int -> int -> 'a -> 'a) -> md256 -> 'a -> 'a
val sei_md256 : (int -> 'a -> int * 'a) -> 'a -> md256 * 'a

val strong_rand_256 : unit -> big_int
val rand_256 : unit -> big_int
