(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hashaux
open Sha256
open Ripemd160
open Ser

type hashval = int32 * int32 * int32 * int32 * int32

let hash160 s = ripemd160_md256 (sha256str s)

let getcurrhashval () = ripemd160_md256 (getcurrmd256())

(*** x:int32 ***)
let hashint32 x =
  sha256init();
  currblock.(0) <- 1l;
  currblock.(1) <- x;
  currblock.(2) <- 0x80000000l;
  currblock.(3) <- 0l;
  currblock.(4) <- 0l;
  currblock.(5) <- 0l;
  currblock.(6) <- 0l;
  currblock.(7) <- 0l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 64l;
  sha256round();
  getcurrhashval()

(*** x:int64 ***)
let hashint64 x =
  sha256init();
  currblock.(0) <- 2l;
  currblock.(1) <- Int64.to_int32 (Int64.shift_right_logical x 32);
  currblock.(2) <- Int64.to_int32 x;
  currblock.(3) <- 0x80000000l;
  currblock.(4) <- 0l;
  currblock.(5) <- 0l;
  currblock.(6) <- 0l;
  currblock.(7) <- 0l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 96l;
  sha256round();
  getcurrhashval()

type addr = int * int32 * int32 * int32 * int32 * int32
type p2pkhaddr = int32 * int32 * int32 * int32 * int32
type p2shaddr = int32 * int32 * int32 * int32 * int32
type payaddr = bool * int32 * int32 * int32 * int32 * int32
type termaddr = int32 * int32 * int32 * int32 * int32
type pubaddr = int32 * int32 * int32 * int32 * int32

let p2pkhaddr_payaddr x =
  let (x0,x1,x2,x3,x4) = x in
  (false,x0,x1,x2,x3,x4)

let p2shaddr_payaddr x =
  let (x0,x1,x2,x3,x4) = x in
  (true,x0,x1,x2,x3,x4)

let p2pkhaddr_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (0,x0,x1,x2,x3,x4)

let p2shaddr_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (1,x0,x1,x2,x3,x4)

let payaddr_addr x =
  let (b,x0,x1,x2,x3,x4) = x in
  if b then
    (1,x0,x1,x2,x3,x4)
  else
    (0,x0,x1,x2,x3,x4)

let termaddr_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (2,x0,x1,x2,x3,x4)

let pubaddr_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (3,x0,x1,x2,x3,x4)

let payaddr_p x =
  let (p,x0,x1,x2,x3,x4) = x in
  p = 0 || p = 1

let p2pkhaddr_p x =
  let (p,x0,x1,x2,x3,x4) = x in
  p = 0

let p2shaddr_p x =
  let (p,x0,x1,x2,x3,x4) = x in
  p = 1

let termaddr_p x =
  let (p,x0,x1,x2,x3,x4) = x in
  p = 2

let pubaddr_p x =
  let (p,x0,x1,x2,x3,x4) = x in
  p = 3

let hashval_bitseq x =
  let (x0,x1,x2,x3,x4) = x in
  let r = ref [] in
  let aux xj =
    for i = 0 to 31 do
      if Int32.logand (Int32.shift_right_logical xj i) 1l = 1l then
	r := true::!r
      else
	r := false::!r
    done
  in
  aux x4; aux x3; aux x2; aux x1; aux x0;
  !r

let hashval_p2pkh_payaddr x =
  let (x0,x1,x2,x3,x4) = x in
  (false,x0,x1,x2,x3,x4)

let hashval_p2sh_payaddr x =
  let (x0,x1,x2,x3,x4) = x in
  (true,x0,x1,x2,x3,x4)

let hashval_p2pkh_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (0,x0,x1,x2,x3,x4)

let hashval_p2sh_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (1,x0,x1,x2,x3,x4)

let hashval_term_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (2,x0,x1,x2,x3,x4)

let hashval_pub_addr x =
  let (x0,x1,x2,x3,x4) = x in
  (3,x0,x1,x2,x3,x4)

let addr_bitseq x =
  let (p,x0,x1,x2,x3,x4) = x in
  let r = hashval_bitseq (x0,x1,x2,x3,x4) in
  if p = 0 then
    (false::false::r)
  else if p = 1 then
    (false::true::r)
  else if p = 2 then
    (true::false::r)
  else
    (true::true::r)

(*** x is an address, 32 bits, represented here as 32 int32s ***)
let hashaddr x =
  let (p,x0,x1,x2,x3,x4) = x in
  sha256init();
  currblock.(0) <- Int32.of_int (3 + p);
  currblock.(1) <- x0;
  currblock.(2) <- x1;
  currblock.(3) <- x2;
  currblock.(4) <- x3;
  currblock.(5) <- x4;
  currblock.(6) <- 0x80000000l;
  currblock.(7) <- 0l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 192l;
  sha256round();
  getcurrhashval()

let hashpayaddr x =
  let (b,x0,x1,x2,x3,x4) = x in
  sha256init();
  currblock.(0) <- if b then 4l else 3l;
  currblock.(1) <- x0;
  currblock.(2) <- x1;
  currblock.(3) <- x2;
  currblock.(4) <- x3;
  currblock.(5) <- x4;
  currblock.(6) <- 0x80000000l;
  currblock.(7) <- 0l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 192l;
  sha256round();
  getcurrhashval()

let hashtermaddr x =
  let (x0,x1,x2,x3,x4) = x in
  sha256init();
  currblock.(0) <- 5l;
  currblock.(1) <- x0;
  currblock.(2) <- x1;
  currblock.(3) <- x2;
  currblock.(4) <- x3;
  currblock.(5) <- x4;
  currblock.(6) <- 0x80000000l;
  currblock.(7) <- 0l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 192l;
  sha256round();
  getcurrhashval()

let hashpubaddr x =
  let (x0,x1,x2,x3,x4) = x in
  sha256init();
  currblock.(0) <- 6l;
  currblock.(1) <- x0;
  currblock.(2) <- x1;
  currblock.(3) <- x2;
  currblock.(4) <- x3;
  currblock.(5) <- x4;
  currblock.(6) <- 0x80000000l;
  currblock.(7) <- 0l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 192l;
  sha256round();
  getcurrhashval()

(*** x and y are hashvals ***)
let hashpair x y =
  let (x0,x1,x2,x3,x4) = x in
  let (y0,y1,y2,y3,y4) = y in
  sha256init();
  currblock.(0) <- 7l;
  currblock.(1) <- x0;
  currblock.(2) <- x1;
  currblock.(3) <- x2;
  currblock.(4) <- x3;
  currblock.(5) <- x4;
  currblock.(6) <- y0;
  currblock.(7) <- y1;
  currblock.(8) <- y2;
  currblock.(9) <- y3;
  currblock.(10) <- y4;
  currblock.(11) <- 0x80000000l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 352l;
  sha256round();
  getcurrhashval()

let hashpubkey x y =
  let (x0,x1,x2,x3,x4,x5,x6,x7) = x in
  let (y0,y1,y2,y3,y4,y5,y6,y7) = y in
  sha256init();
  currblock.(0) <- Int32.logor (Int32.shift_left 4l 24) (Int32.shift_right_logical x0 8);
  currblock.(1) <- Int32.logor (Int32.shift_left x0 24) (Int32.shift_right_logical x1 8);
  currblock.(2) <- Int32.logor (Int32.shift_left x1 24) (Int32.shift_right_logical x2 8);
  currblock.(3) <- Int32.logor (Int32.shift_left x2 24) (Int32.shift_right_logical x3 8);
  currblock.(4) <- Int32.logor (Int32.shift_left x3 24) (Int32.shift_right_logical x4 8);
  currblock.(5) <- Int32.logor (Int32.shift_left x4 24) (Int32.shift_right_logical x5 8);
  currblock.(6) <- Int32.logor (Int32.shift_left x5 24) (Int32.shift_right_logical x6 8);
  currblock.(7) <- Int32.logor (Int32.shift_left x6 24) (Int32.shift_right_logical x7 8);
  currblock.(8) <- Int32.logor (Int32.shift_left x7 24) (Int32.shift_right_logical y0 8);
  currblock.(9) <- Int32.logor (Int32.shift_left y0 24) (Int32.shift_right_logical y1 8);
  currblock.(10) <- Int32.logor (Int32.shift_left y1 24) (Int32.shift_right_logical y2 8);
  currblock.(11) <- Int32.logor (Int32.shift_left y2 24) (Int32.shift_right_logical y3 8);
  currblock.(12) <- Int32.logor (Int32.shift_left y3 24) (Int32.shift_right_logical y4 8);
  currblock.(13) <- Int32.logor (Int32.shift_left y4 24) (Int32.shift_right_logical y5 8);
  currblock.(14) <- Int32.logor (Int32.shift_left y5 24) (Int32.shift_right_logical y6 8);
  currblock.(15) <- Int32.logor (Int32.shift_left y6 24) (Int32.shift_right_logical y7 8);
  sha256round();
  currblock.(0) <- Int32.logor (Int32.shift_left y7 24) 0x800000l;
  currblock.(1) <- 0l;
  currblock.(2) <- 0l;
  currblock.(3) <- 0l;
  currblock.(4) <- 0l;
  currblock.(5) <- 0l;
  currblock.(6) <- 0l;
  currblock.(7) <- 0l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 520l;
  sha256round();
  getcurrhashval()

let hashpubkeyc p x =
  let (x0,x1,x2,x3,x4,x5,x6,x7) = x in
  sha256init();
  currblock.(0) <- Int32.logor (Int32.shift_left (Int32.of_int p) 24) (Int32.shift_right_logical x0 8);
  currblock.(1) <- Int32.logor (Int32.shift_left x0 24) (Int32.shift_right_logical x1 8);
  currblock.(2) <- Int32.logor (Int32.shift_left x1 24) (Int32.shift_right_logical x2 8);
  currblock.(3) <- Int32.logor (Int32.shift_left x2 24) (Int32.shift_right_logical x3 8);
  currblock.(4) <- Int32.logor (Int32.shift_left x3 24) (Int32.shift_right_logical x4 8);
  currblock.(5) <- Int32.logor (Int32.shift_left x4 24) (Int32.shift_right_logical x5 8);
  currblock.(6) <- Int32.logor (Int32.shift_left x5 24) (Int32.shift_right_logical x6 8);
  currblock.(7) <- Int32.logor (Int32.shift_left x6 24) (Int32.shift_right_logical x7 8);
  currblock.(8) <- Int32.logor (Int32.shift_left x7 24) 0x800000l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 264l;
  sha256round();
  getcurrhashval()

let hashtag x tg =
  let (x0,x1,x2,x3,x4) = x in
  sha256init();
  currblock.(0) <- 8l;
  currblock.(1) <- tg;
  currblock.(2) <- x0;
  currblock.(3) <- x1;
  currblock.(4) <- x2;
  currblock.(5) <- x3;
  currblock.(6) <- x4;
  currblock.(7) <- 0x80000000l;
  currblock.(8) <- 0l;
  currblock.(9) <- 0l;
  currblock.(10) <- 0l;
  currblock.(11) <- 0l;
  currblock.(12) <- 0l;
  currblock.(13) <- 0l;
  currblock.(14) <- 0l;
  currblock.(15) <- 224l;
  sha256round();
  getcurrhashval()

let hashlist hl =
  let l = List.length hl in
  if l >= 8388576 then raise (Failure "hashlist overflow");
  let bl = Int32.of_int (l * 160 + 64) in
  sha256init();
  currblock.(0) <- 9l;
  currblock.(1) <- Int32.of_int l;
  let i = ref 2 in
  List.iter
    (fun x ->
      let (x0,x1,x2,x3,x4) = x in
      currblock.(!i) <- x0;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x1;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x2;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x3;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x4;
      incr i;
      if !i = 16 then (i := 0; sha256round());
    ) hl;
  if !i < 15 then
    begin
      currblock.(!i) <- 0x80000000l;
      incr i;
      while !i < 15 do
	currblock.(!i) <- 0l;
	incr i;
      done
    end
  else
    begin
      currblock.(15) <- 0x80000000l;
      sha256round();
      for j = 0 to 14 do
	currblock.(j) <- 0l;
      done
    end;
  currblock.(15) <- bl;
  sha256round();
  getcurrhashval()

let hashfold f al =
  let l = List.length al in
  if l >= 8388576 then raise (Failure "hashlist overflow");
  let bl = Int32.of_int (l * 160 + 64) in
  sha256init();
  currblock.(0) <- 10l;
  currblock.(1) <- Int32.of_int l;
  let i = ref 2 in
  List.iter
    (fun a ->
      let (x0,x1,x2,x3,x4) = f a in
      currblock.(!i) <- x0;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x1;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x2;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x3;
      incr i;
      if !i = 16 then (i := 0; sha256round());
      currblock.(!i) <- x4;
      incr i;
      if !i = 16 then (i := 0; sha256round());
    ) al;
  if !i < 15 then
    begin
      currblock.(!i) <- 0x80000000l;
      incr i;
      while !i < 15 do
	currblock.(!i) <- 0l;
	incr i;
      done
    end
  else
    begin
      currblock.(15) <- 0x80000000l;
      sha256round();
      for j = 0 to 14 do
	currblock.(j) <- 0l;
      done
    end;
  currblock.(15) <- bl;
  sha256round();
  getcurrhashval()

let rec ohashlist hl =
  begin
    match hl with
    | [] -> None
    | h::hr ->
	begin
	  match ohashlist hr with
	  | None -> Some(hashtag h 3l)
	  | Some(k) -> Some(hashtag (hashpair h k) 4l)
	end
  end
    
(*** hashopair, x and y are hashval options ***)
let hashopair x y =
  match x,y with
  | Some x,Some y -> Some(hashpair x y)
  | Some x,None -> Some(hashtag x 0l)
  | None,Some y -> Some(hashtag y 1l)
  | None,None -> None

let hashopair1 x y =
  match y with
  | Some y -> hashpair x y
  | None -> hashtag x 0l

let hashopair2 x y =
  match x with
  | Some x -> hashpair x y
  | None -> hashtag y 1l

let hashval_hexstring h =
  let b = Buffer.create 64 in
  let (h0,h1,h2,h3,h4) = h in
  int32_hexstring b h0;
  int32_hexstring b h1;
  int32_hexstring b h2;
  int32_hexstring b h3;
  int32_hexstring b h4;
  Buffer.contents b

let hexstring_hashval h =
  (hexsubstring_int32 h 0,hexsubstring_int32 h 8,hexsubstring_int32 h 16,hexsubstring_int32 h 24,hexsubstring_int32 h 32)

let printhashval h =
  Printf.printf "%s\n" (hashval_hexstring h)

let hashval_rev h =
  let (h0,h1,h2,h3,h4) = h in
  (int32_rev h4,int32_rev h3,int32_rev h2,int32_rev h1,int32_rev h0)

let hashval_big_int h =
  let (h0,h1,h2,h3,h4) = h in
  let x0 = int32_big_int_bits h0 128 in
  let x1 = or_big_int x0 (int32_big_int_bits h1 96) in
  let x2 = or_big_int x1 (int32_big_int_bits h2 64) in
  let x3 = or_big_int x2 (int32_big_int_bits h3 32) in
  or_big_int x3 (int32_big_int_bits h4 0)

let big_int_hashval x =
  let h0 = big_int_sub_int32 x 128 in
  let h1 = big_int_sub_int32 x 96 in
  let h2 = big_int_sub_int32 x 64 in
  let h3 = big_int_sub_int32 x 32 in
  let h4 = big_int_sub_int32 x 0 in
  (h0,h1,h2,h3,h4)

let seo_hashval o h c =
  let (h0,h1,h2,h3,h4) = h in
  let c = seo_int32 o h0 c in
  let c = seo_int32 o h1 c in
  let c = seo_int32 o h2 c in
  let c = seo_int32 o h3 c in
  let c = seo_int32 o h4 c in
  c

let sei_hashval i c =
  let (h0,c) = sei_int32 i c in
  let (h1,c) = sei_int32 i c in
  let (h2,c) = sei_int32 i c in
  let (h3,c) = sei_int32 i c in
  let (h4,c) = sei_int32 i c in
  ((h0,h1,h2,h3,h4),c)

let seo_addr o (p,x0,x1,x2,x3,x4) c =
  let c = o 2 p c in (*** 2 bit prefix indicating which kind of address ***)
  seo_hashval o (x0,x1,x2,x3,x4) c

let sei_addr i c =
  let (p,c) = i 2 c in
  let ((x0,x1,x2,x3,x4),c) = sei_hashval i c in
  ((p,x0,x1,x2,x3,x4),c)

let seo_payaddr o (b,x0,x1,x2,x3,x4) c =
  let c = o 1 (if b then 1 else 0) c in (*** 1 bit prefix indicating whether its p2pkh or p2sh ***)
  seo_hashval o (x0,x1,x2,x3,x4) c

let sei_payaddr i c =
  let (b,c) = i 1 c in
  let ((x0,x1,x2,x3,x4),c) = sei_hashval i c in
  ((b = 1,x0,x1,x2,x3,x4),c)

let seo_termaddr o alpha c = seo_hashval o alpha c
let sei_termaddr i c = sei_hashval i c
let seo_pubaddr o alpha c = seo_hashval o alpha c
let sei_pubaddr i c = sei_hashval i c


