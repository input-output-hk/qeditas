(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hashaux

(*** Following
 Dobbertin, Bosselaers, Preneel. 1996
 RIPEMD-160: A Strengthened Veripemd.
 With some constants taken from rosettacode.org/wiki/RIPEMD-160
 ***)

let f0 x y z = Int32.logxor x (Int32.logxor y z)
let f1 x y z = Int32.logor (Int32.logand x y) (Int32.logand (Int32.lognot x) z)
let f2 x y z = Int32.logxor (Int32.logor x (Int32.lognot y)) z
let f3 x y z = Int32.logor (Int32.logand x z) (Int32.logand y (Int32.lognot z))
let f4 x y z = Int32.logxor x (Int32.logor y (Int32.lognot z))

let ripemd160consts1 : int32 array = [| 0x00000000l; 0x5a827999l; 0x6ed9eba1l; 0x8f1bbcdcl; 0xa953fd4el |]
let ripemd160consts2 : int32 array = [| 0x50a28be6l; 0x5c4dd124l; 0x6d703ef3l; 0x7a6d76e9l; 0x00000000l |]

let r1 = [| 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15;
	    7; 4; 13; 1; 10; 6; 15; 3; 12; 0; 9; 5; 2; 14; 11; 8;
	    3; 10; 14; 4; 9; 15; 8; 1; 2; 7; 0; 6; 13; 11; 5; 12;
	    1; 9; 11; 10; 0; 8; 12; 4; 13; 3; 7; 15; 14; 5; 6; 2;
	    4; 0; 5; 9; 7; 12; 2; 10; 14; 1; 3; 8; 11; 6; 15; 13 |]

let r2 = [| 5; 14; 7; 0; 9; 2; 11; 4; 13; 6; 15; 8; 1; 10; 3; 12;
	    6; 11; 3; 7; 0; 13; 5; 10; 14; 15; 8; 12; 4; 9; 1; 2;
	    15; 5; 1; 3; 7; 14; 6; 9; 11; 8; 12; 2; 10; 0; 4; 13;
	    8; 6; 4; 1; 3; 11; 15; 0; 5; 12; 2; 13; 9; 7; 10; 14;
	    12; 15; 10; 4; 1; 5; 8; 7; 6; 2; 13; 14; 0; 3; 9; 11 |]

let s1 = [| 11; 14; 15; 12; 5; 8; 7; 9; 11; 13; 14; 15; 6; 7; 9; 8;
	    7; 6; 8; 13; 11; 9; 7; 15; 7; 12; 15; 9; 11; 7; 13; 12;
	    11; 13; 6; 7; 14; 9; 13; 15; 14; 8; 13; 6; 5; 12; 7; 5;
	    11; 12; 14; 15; 14; 15; 9; 8; 9; 14; 5; 6; 8; 6; 5; 12;
	    9; 15; 5; 11; 6; 8; 13; 12; 5; 12; 13; 14; 11; 8; 5; 6 |]

let s2 = [| 8; 9; 9; 11; 13; 15; 15; 5; 7; 7; 8; 11; 14; 14; 12; 6;
	    9; 13; 15; 7; 12; 8; 9; 11; 7; 7; 12; 7; 6; 15; 13; 11;
	    9; 7; 15; 11; 8; 6; 6; 14; 12; 13; 5; 14; 13; 13; 7; 5;
	    15; 5; 8; 11; 14; 14; 6; 14; 6; 9; 12; 9; 12; 5; 15; 8;
	    8; 5; 12; 9; 12; 5; 14; 6; 8; 13; 6; 5; 15; 13; 11; 11 |]

let currmd : int32 array = [| 0x67452301l; 0xefcdab89l; 0x98badcfel; 0x10325476l; 0xc3d2e1f0l; |]

let currblock : int32 array = [|
  0x0l; 0x0l; 0x0l; 0x0l; 0x0l; 0x0l; 0x0l; 0x0l;
  0x0l; 0x0l; 0x0l; 0x0l; 0x0l; 0x0l; 0x0l; 0x0l |]

let a = ref 0l
let b = ref 0l
let c = ref 0l
let d = ref 0l
let e = ref 0l
let a2 = ref 0l
let b2 = ref 0l
let c2 = ref 0l
let d2 = ref 0l
let e2 = ref 0l

let int32_left_rotation x n =
  Int32.logor (Int32.shift_right_logical x (32 - n)) (Int32.shift_left x n)

let ripemd160init () =
  currmd.(0) <- 0x67452301l;
  currmd.(1) <- 0xefcdab89l;
  currmd.(2) <- 0x98badcfel;
  currmd.(3) <- 0x10325476l;
  currmd.(4) <- 0xc3d2e1f0l

let ripemd160round t =
  a := currmd.(0);
  b := currmd.(1);
  c := currmd.(2);
  d := currmd.(3);
  e := currmd.(4);
  a2 := currmd.(0);
  b2 := currmd.(1);
  c2 := currmd.(2);
  d2 := currmd.(3);
  e2 := currmd.(4);
  for j = 0 to 79 do
    let j2 = j lsr 4 in
    let (fj,fnj) =
      begin
	match j2 with
	| 0 -> (f0,f4)
	| 1 -> (f1,f3)
	| 2 -> (f2,f2)
	| 3 -> (f3,f1)
	| 4 -> (f4,f0)
	| _ -> raise (Failure("Something impossible happened in ripemd160"))
      end
    in
    let t = Int32.add
	(int32_left_rotation (Int32.add !a (Int32.add (fj !b !c !d) (Int32.add currblock.(r1.(j)) ripemd160consts1.(j2)))) s1.(j))
	!e
    in
    a := !e; e := !d; d := int32_left_rotation !c 10; c := !b; b := t;
    let t = Int32.add
	(int32_left_rotation (Int32.add !a2 (Int32.add (fnj !b2 !c2 !d2) (Int32.add currblock.(r2.(j)) ripemd160consts2.(j2)))) s2.(j))
	!e2
    in
    a2 := !e2; e2 := !d2; d2 := int32_left_rotation !c2 10; c2 := !b2; b2 := t;
  done;
  let t = Int32.add (currmd.(1)) (Int32.add !c !d2) in
  currmd.(1) <- Int32.add currmd.(2) (Int32.add !d !e2);
  currmd.(2) <- Int32.add currmd.(3) (Int32.add !e !a2);
  currmd.(3) <- Int32.add currmd.(4) (Int32.add !a !b2);
  currmd.(4) <- Int32.add currmd.(0) (Int32.add !b !c2);
  currmd.(0) <- t

type md = int32 * int32 * int32 * int32 * int32

let getcurrmd () : md =
  (int32_rev currmd.(0),int32_rev currmd.(1),int32_rev currmd.(2),int32_rev currmd.(3),int32_rev currmd.(4))

let md_hexstring h =
  let b = Buffer.create 64 in
  let (h0,h1,h2,h3,h4) = h in
  int32_hexstring b h0;
  int32_hexstring b h1;
  int32_hexstring b h2;
  int32_hexstring b h3;
  int32_hexstring b h4;
  Buffer.contents b

let printmd h =
  Printf.printf "%s" (md_hexstring h)

let hexstring_md h =
  (hexsubstring_int32 h 0,hexsubstring_int32 h 8,hexsubstring_int32 h 16,hexsubstring_int32 h 24,hexsubstring_int32 h 32)

let ripemd160_md256 h =
  let (h0,h1,h2,h3,h4,h5,h6,h7) = h in
  currblock.(0) <- int32_rev h0;
  currblock.(1) <- int32_rev h1;
  currblock.(2) <- int32_rev h2;
  currblock.(3) <- int32_rev h3;
  currblock.(4) <- int32_rev h4;
  currblock.(5) <- int32_rev h5;
  currblock.(6) <- int32_rev h6;
  currblock.(7) <- int32_rev h7;
  currblock.(8) <- 0x80l;
  currblock.(9) <- 0x0l;
  currblock.(10) <- 0x0l;
  currblock.(11) <- 0x0l;
  currblock.(12) <- 0x0l;
  currblock.(13) <- 0x0l;
  currblock.(14) <- 256l;
  currblock.(15) <- 0l;
  ripemd160init();
  ripemd160round();
  getcurrmd ()

