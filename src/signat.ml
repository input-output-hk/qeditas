(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Ser
open Sha256
open Hash
open Secp256k1
open Cryptocurr

type signat = big_int * big_int

(*** Following code in util.cpp in bitcoin ***)
let decode64table = [|
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; 62; -1; -1; -1; 63; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; -1; -1;
        -1; -1; -1; -1; -1;  0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14;
        15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; -1; -1; -1; -1; -1; -1; 26; 27; 28;
        29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48;
        49; 50; 51; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1;
        -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1
 |];;

let base64decode_end s l i mode lft =
  if mode = 0 then (*** something extra is in the string, but shouldn't be. ***)
    raise (Failure("not a proper base64 string 0"))
  else if mode = 1 then (*** 4n+1 base64 character processed: according to util.ccp, this is impossible ***)
    raise (Failure("not a proper base64 string 1"))
  else if mode = 2 then (*** 4n+2 base64 characters processed: according to util.cpp, require '==' ***)
    if l = i + 2 && lft = 0 && s.[i] = '=' && s.[i+1] = '=' then
      []
    else
      raise (Failure("not a proper base64 string 2"))
  else if mode = 3 then (*** 4n+3 base64 characters processed: according to util.cpp, require '=' ***)
    if l = i + 1 && lft = 0 && s.[i] = '=' then
      []
    else
      raise (Failure("not a proper base64 string 3"))
  else (*** should never happen ***)
    raise (Failure("not a proper base64 string"))

let rec base64decode_a s l i mode lft =
  if i < l then
    let dec = decode64table.(Char.code(s.[i])) in
    if dec = -1 then
      base64decode_end s l i mode lft
    else
      if mode = 0 then
	base64decode_a s l (i+1) 1 dec
      else if mode = 1 then
	((lft lsl 2) lor (dec lsr 4))::(base64decode_a s l (i+1) 2 (dec land 15))
      else if mode = 2 then
	((lft lsl 4) lor (dec lsr 2))::(base64decode_a s l (i+1) 3 (dec land 3))
      else
	((lft lsl 6) lor dec)::(base64decode_a s l (i+1) 0 0)
  else if mode = 0 then
    []
  else
    raise (Failure("base64 string ended in wrong mode"))

let base64decode s =
  base64decode_a s (String.length s) 0 0 0

let rec bytelist_to_big_int rst n c =
  if n > 0 then
    match rst with
    | (b::rst2) -> bytelist_to_big_int rst2 (n-1) (or_big_int (shift_left_big_int (big_int_of_int b) ((n-1)*8)) c)
    | [] -> raise (Failure("not enough bytes"))
  else
    (c,rst)

let decode_signature sg =
  match base64decode sg with
  | (by0::rst) ->
      let (r,rst2) = bytelist_to_big_int rst 32 zero_big_int in
      let (s,rst3) = bytelist_to_big_int rst2 32 zero_big_int in
      if rst3 = [] then
	(by0,(r,s))
      else
	raise (Failure("Signature Too Long"))
  | [] -> raise (Failure("Empty Signature"))

let decode_signature_a sg =
  let (by0,(r,s)) = decode_signature sg in
  let by27 = by0-27 in
  let recid = by27 land 3 in
  let fcomp = by27 land 4 > 0 in
  (recid,fcomp,(r,s))
  
(** * Digital Signatures for Qeditas ***)
exception ZeroValue

let inv_gen x q =
  let (u,v) = eea q (mod_big_int x q) in
  mod_big_int v q

let signat_big_int e privk randk =
  match smulp randk _g with
  | Some(xr,yr) ->
      let r = mod_big_int xr _n in
      if r = zero_big_int then raise ZeroValue;
      let s = mod_big_int (mult_big_int (inv_gen randk _n) (add_big_int e (mult_big_int r privk))) _n in
      if s = zero_big_int then raise ZeroValue;
      (r,s)
  | None -> raise ZeroValue

let verify_signed_big_int e q (r,s) =
  if lt_big_int r _n && lt_big_int s _n && lt_big_int e _p then
    let sinv = inv_gen s _n in
    let u1 = mod_big_int (mult_big_int e sinv) _n in
    let u2 = mod_big_int (mult_big_int r sinv) _n in
    match addp (smulp u1 _g) (smulp u2 q) with
    | None -> false
    | Some(xr,yr) -> eq_big_int (mod_big_int xr _n) r
  else
    false

let signat_hashval h privk randk = signat_big_int (hashval_big_int h) privk randk

let verify_signed_hashval h q (r,s) = verify_signed_big_int (hashval_big_int h) q (r,s)

(*** The pow function from Egal only works for int exponents, but sqrtp needs it for a big int ***)
let rec bigpow_p x m =
  if gt_big_int m zero_big_int then
    let z = bigpow_p (mul x x) (shift_right_towards_zero_big_int m 1) in
    if evenp m then
      z
    else
      mul z x
  else
    unit_big_int

let sqrtp a =
  bigpow_p a (div_big_int (add_big_int unit_big_int _p) (big_int_of_int 4))

let curve_y x = sqrtp (add (pow x 3) (big_int_of_int 7))

let _minusg = Some(big_int_of_string "55066263022277343669578718895168534326250603453777594175500187360389116729240",
		 big_int_of_string "83121579216557378445487899878180864668798711284981320763518679672151497189239")
		 
let recover_key e (r,s) recid =
  let xr = if recid > 1 then mod_big_int (add_big_int r _n) _p else r in
  let yr1 = curve_y xr in
  let yr = if (recid mod 2 = 0) = (evenp yr1) then yr1 else sub_big_int _p yr1 in
  let rinv = inv_gen r _n in
  smulp rinv (addp (smulp s (Some(xr,yr))) (smulp e _minusg))

let verify_p2pkhaddr_signat e alpha (r,s) recid fcomp =
  match recover_key e (r,s) recid with
  | Some(q) -> pubkey_hashval q fcomp = alpha
  | None -> false

let verifymessage_a alpha recid fcomp (r,s) m =
  let e = md256_big_int (sha256dstr m) in
  match recover_key e (r,s) recid with
  | Some(q) -> pubkey_hashval q fcomp = alpha
  | None -> false

let verifymessage alpha by0 (r,s) m =
  let by27 = by0-27 in
  let recid = by27 land 3 in
  let fcomp = by27 land 4 > 0 in
  verifymessage_a alpha recid fcomp (r,s) m

let verifymessage_base64 alpha sg m =
  let (by0,(r,s)) = decode_signature sg in
  verifymessage alpha by0 (r,s) m

let md256_of_bitcoin_message m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  sha256dstr (Buffer.contents ms)

let verifybitcoinmessage_a alpha recid fcomp (r,s) m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  verifymessage_a alpha recid fcomp (r,s) (Buffer.contents ms)

let verifybitcoinmessage alpha by0 (r,s) m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  verifymessage alpha by0 (r,s) (Buffer.contents ms)

let verifybitcoinmessage_base64 alpha sg m =
  let (by0,(r,s)) = decode_signature sg in
  verifybitcoinmessage alpha by0 (r,s) m

let seo_signat o rs c = seo_prod seo_big_int_256 seo_big_int_256 o rs c
let sei_signat i c = sei_prod sei_big_int_256 sei_big_int_256 i c
