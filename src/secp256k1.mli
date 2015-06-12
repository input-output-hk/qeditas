(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2014 Chad E Brown *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* This code for secp256k1 is directly taken from Egal. *)

(* Code for the Elliptic Curve secp256k1 *)
(* https://en.bitcoin.it/wiki/Secp256k1 *)

(* Use the Big_int library for arbitrary-precision integers. *)
open Big_int

val evenp : big_int -> bool
val oddp : big_int -> bool

(* _p : the 256 bit int prime in secp256k1 *)
val _p : big_int

(* operations module _p *)
val eea : big_int -> big_int -> big_int * big_int
val mul : big_int -> big_int -> big_int
val add : big_int -> big_int -> big_int
val pow : big_int -> int -> big_int

(* Intended to be points on the curve y^2 = x^3 + 7 *)
(* None is used for the zero point/point at infinity *)
type pt = (big_int * big_int) option

(* addition of two points *)
val addp : pt -> pt -> pt

(* scalar multiplication *)
val smulp : big_int -> pt -> pt

(* base point _g *)
val _g : pt

(* _n : order of _g *)
val _n : big_int
