(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

type seosbt = Buffer.t * (int * int) option
type seist = string * int * int option * int * int

val seosb : int -> int -> seosbt -> seosbt
val seosbf : seosbt -> unit

val seis : int -> seist -> int * seist

type seoct = out_channel * (int * int) option
type seict = in_channel * (int * int) option

val seoc : int -> int -> seoct -> seoct
val seocf : seoct -> unit

val seic : int -> seict -> int * seict

val seo_bool : (int -> int -> 'a -> 'a) -> bool -> 'a -> 'a
val sei_bool : (int -> 'a -> int * 'a) -> 'a -> bool * 'a

val seo_int32 : (int -> int -> 'a -> 'a) -> int32 -> 'a -> 'a
val sei_int32 : (int -> 'a -> int * 'a) -> 'a -> int32 * 'a

val seo_int64 : (int -> int -> 'a -> 'a) -> int64 -> 'a -> 'a
val sei_int64 : (int -> 'a -> int * 'a) -> 'a -> int64 * 'a

val seo_varint : (int -> int -> 'a -> 'a) -> int64 -> 'a -> 'a
val sei_varint : (int -> 'a -> int * 'a) -> 'a -> int64 * 'a

val seo_varintb : (int -> int -> 'a -> 'a) -> int -> 'a -> 'a
val sei_varintb : (int -> 'a -> int * 'a) -> 'a -> int * 'a

val seo_list : ((int -> int -> 'a -> 'a) -> 'b -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'b list -> 'a -> 'a)
val sei_list : ((int -> 'a -> int * 'a) -> 'a -> 'b * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'b list * 'a)

val seo_option : ((int -> int -> 'a -> 'a) -> 'b -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'b option -> 'a -> 'a)
val sei_option : ((int -> 'a -> int * 'a) -> 'a -> 'b * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'b option * 'a)

val seo_prod : ((int -> int -> 'a -> 'a) -> 'b -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'c -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'b * 'c -> 'a -> 'a)
val sei_prod : ((int -> 'a -> int * 'a) -> 'a -> 'b * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'c * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> ('b * 'c) * 'a)

val seo_prod3 : ((int -> int -> 'a -> 'a) -> 'b -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'c -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'd -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'b * 'c * 'd -> 'a -> 'a)
val sei_prod3 : ((int -> 'a -> int * 'a) -> 'a -> 'b * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'c * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'd * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> ('b * 'c * 'd) * 'a)

val seo_prod4 : ((int -> int -> 'a -> 'a) -> 'b -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'c -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'd -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'e -> 'a -> 'a) -> ((int -> int -> 'a -> 'a) -> 'b * 'c * 'd * 'e -> 'a -> 'a)
val sei_prod4 : ((int -> 'a -> int * 'a) -> 'a -> 'b * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'c * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'd * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> 'e * 'a) -> ((int -> 'a -> int * 'a) -> 'a -> ('b * 'c * 'd * 'e) * 'a)
