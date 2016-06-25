(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* Most of this code is taken directly from Egal. *)

open Big_int
open Ser
open Hashaux
open Sha256
open Hash
open Secp256k1

(* base58 representation *)
let _base58strs = ["1";"2";"3";"4";"5";"6";"7";"8";"9";"A";"B";"C";"D";"E";"F";"G";"H";"J";"K";"L";"M";"N";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]

(* c : big_int *)
(* return base58 string representation of c *)
let rec base58_rec c r =
  if gt_big_int c zero_big_int then
    let (q,m) = quomod_big_int c (big_int_of_string "58") in
    base58_rec q ((List.nth _base58strs (int_of_big_int m)) ^ r)
  else
    r

let base58 c = base58_rec c ""

let base58char_int c =
   match c with
   | '1' -> 0
   | '2' -> 1
   | '3' -> 2
   | '4' -> 3
   | '5' -> 4
   | '6' -> 5
   | '7' -> 6
   | '8' -> 7
   | '9' -> 8
   | 'A' -> 9
   | 'B' -> 10
   | 'C' -> 11
   | 'D' -> 12
   | 'E' -> 13
   | 'F' -> 14
   | 'G' -> 15
   | 'H' -> 16
   | 'J' -> 17
   | 'K' -> 18
   | 'L' -> 19
   | 'M' -> 20
   | 'N' -> 21
   | 'P' -> 22
   | 'Q' -> 23
   | 'R' -> 24
   | 'S' -> 25
   | 'T' -> 26
   | 'U' -> 27
   | 'V' -> 28
   | 'W' -> 29
   | 'X' -> 30
   | 'Y' -> 31
   | 'Z' -> 32
   | 'a' -> 33
   | 'b' -> 34
   | 'c' -> 35
   | 'd' -> 36
   | 'e' -> 37
   | 'f' -> 38
   | 'g' -> 39
   | 'h' -> 40
   | 'i' -> 41
   | 'j' -> 42
   | 'k' -> 43
   | 'm' -> 44
   | 'n' -> 45
   | 'o' -> 46
   | 'p' -> 47
   | 'q' -> 48
   | 'r' -> 49
   | 's' -> 50
   | 't' -> 51
   | 'u' -> 52
   | 'v' -> 53
   | 'w' -> 54
   | 'x' -> 55
   | 'y' -> 56
   | 'z' -> 57
   | _ -> raise (Failure "bad base58 char")

(* s : base58 string *)
(* return int representation of s *)
let rec frombase58_rec s i sl r =
  if i < sl then
    frombase58_rec s (i + 1) sl (add_int_big_int (base58char_int (String.get s i)) (mult_int_big_int 58 r))
  else
    r

let frombase58 s = frombase58_rec s 0 (String.length s) zero_big_int

(* Computation of Wallet Import Formats for Private Keys *)

(* wifs for qeditas private keys use two prefix bytes 1288 (for compressed, start with k) or 542 (for uncompressed, start with K) *)
(* k : private key, big_int *)
(* return string, base58 btc wif *)
let qedwif k compr =
  let (pc1,pc2,pre) = if compr then ('\005','\008',1288) else ('\002','\030',542) in
  let s = Buffer.create 34 in
  Buffer.add_char s pc1;
  Buffer.add_char s pc2;
  let c = seo_md256 seosb (big_int_md256 k) (s,None) in
  seosbf c;
  let (sh20,_,_,_,_,_,_,_) = sha256dstr (Buffer.contents s) in
  base58 (or_big_int (shift_left_big_int (or_big_int k (shift_left_big_int (big_int_of_int pre) 256)) 32) (int32_big_int_bits sh20 0))

(* w : Qeditas wif base58 string *)
(* return private key, big_int and a bool indicating if it's for the compressed pubkey *)
(* Note: This doesn't check the checksum. *)
let privkey_from_wif w =
  let k =
    and_big_int (shift_right_towards_zero_big_int (frombase58 w) 32)
      (big_int_of_string "115792089237316195423570985008687907853269984665640564039457584007913129639935")
  in
  let pre = int_of_big_int (shift_right_towards_zero_big_int (frombase58 w) 288) in
  if pre = 1288 then
    (k,true)
  else if pre = 542 then
    (k,false)
  else
    raise (Failure "Invalid Qeditas WIF")

(* w : Bitcoin wif base58 string *)
(* return private key, big_int and a bool indicating if it's for the compressed pubkey *)
(* Note: This doesn't check the checksum. *)
let privkey_from_btcwif w =
  if String.length w > 1 && w.[0] = '5' then
    let k =
      and_big_int (shift_right_towards_zero_big_int (frombase58 w) 32)
	(big_int_of_string "115792089237316195423570985008687907853269984665640564039457584007913129639935")
    in
    (k,false)
  else
    let k =
      and_big_int (shift_right_towards_zero_big_int (frombase58 w) 40)
	(big_int_of_string "115792089237316195423570985008687907853269984665640564039457584007913129639935")
    in
    (k,true)

(* Computation of base 58 address strings *)

let count_int32_bytes x =
  if x < 0l then
    0
  else if x = 0l then
    4
  else if x < 256l then
    3
  else if x < 65536l then
    2
  else if x < 16777216l then
    1
  else
    0

(* Helper function to count the leading 0 bytes. btcaddr uses this. *)
let count0bytes (x0,x1,x2,x3,x4) =
  if x0 = 0l then
    if x1 = 0l then
      if x2 = 0l then
	if x3 = 0l then
	  if x4 = 0l then
	    20
	  else
	    16 + count_int32_bytes x4
	else
	  12 + count_int32_bytes x3
      else
	8 + count_int32_bytes x2
    else
      4 + count_int32_bytes x1
  else
    count_int32_bytes x0

let pubkey_hashval (x,y) compr =
  if compr then
    hashpubkeyc (if evenp y then 2 else 3) (big_int_md256 x)
  else
    hashpubkey (big_int_md256 x) (big_int_md256 y)

let hashval_from_addrstr b =
  let (_,_,x0,x1,x2,x3,x4,_) = big_int_md256 (frombase58 b) in
  (x0,x1,x2,x3,x4)

let calc_checksum pre rm1 =
  let s = Buffer.create 21 in
  Buffer.add_char s (Char.chr (pre mod 256));
  let c = seo_hashval seosb rm1 (s,None) in
  seosbf c;
  let (sh30,_,_,_,_,_,_,_) = sha256dstr (Buffer.contents s) in
  sh30

let qedaddrstr_addr b =
  let (_,p,x0,x1,x2,x3,x4,cksm) = big_int_md256 (frombase58 b) in
  if p < 0l || p > 8000l then raise (Failure "Not a valid Qeditas address (bad prefix)");
  if not (cksm = calc_checksum (Int32.to_int p) (x0,x1,x2,x3,x4)) then raise (Failure "Not a valid Qeditas address (checksum incorrect)");
  if p = 58l then
    if !Config.testnet then raise (Failure "Qeditas mainnet address given while using testnet") else (0,x0,x1,x2,x3,x4)
  else if p = 120l then
    if !Config.testnet then raise (Failure "Qeditas mainnet address given while using testnet") else (1,x0,x1,x2,x3,x4)
  else if p = 66l then
    if !Config.testnet then raise (Failure "Qeditas mainnet address given while using testnet") else (2,x0,x1,x2,x3,x4)
  else if p = 56l then
    if !Config.testnet then raise (Failure "Qeditas mainnet address given while using testnet") else (3,x0,x1,x2,x3,x4)
  else if p = 7409l then
    if not !Config.testnet then raise (Failure "Qeditas testnet address given while using mainnet") else (0,x0,x1,x2,x3,x4)
  else if p = 7471l then
    if not !Config.testnet then raise (Failure "Qeditas testnet address given while using mainnet") else (1,x0,x1,x2,x3,x4)
  else if p = 7416l then
    if not !Config.testnet then raise (Failure "Qeditas testnet address given while using mainnet") else (2,x0,x1,x2,x3,x4)
  else if p = 7406l then
    if not !Config.testnet then raise (Failure "Qeditas testnet address given while using mainnet") else (3,x0,x1,x2,x3,x4)
  else
    raise (Failure "Not a Qeditas address")

let btcaddrstr_addr b =
  let (_,p,x0,x1,x2,x3,x4,_) = big_int_md256 (frombase58 b) in
  if p = 0l then
    (0,x0,x1,x2,x3,x4)
  else if p = 5l then
    (1,x0,x1,x2,x3,x4)
  else
    raise (Failure "Not a Bitcoin address")

let hashval_btcaddrstr rm1 =
  let c0 = count0bytes rm1 in
  let s = Buffer.create 21 in
  Buffer.add_char s '\000';
  let c = seo_hashval seosb rm1 (s,None) in
  seosbf c;
  let (sh30,_,_,_,_,_,_,_) = sha256dstr (Buffer.contents s) in
  let (rm10,rm11,rm12,rm13,rm14) = rm1 in
  let a = md256_big_int (0l,0l,rm10,rm11,rm12,rm13,rm14,sh30) in
  ((String.make (c0+1) '1') ^ (base58 a))

let hashval_gen_addrstr pre rm1 =
  let sh30 = calc_checksum pre rm1 in
  let (rm10,rm11,rm12,rm13,rm14) = rm1 in
  let a = md256_big_int (0l,Int32.of_int pre,rm10,rm11,rm12,rm13,rm14,sh30) in
  base58 a

let addr_qedaddrstr alpha =
  let (p,x0,x1,x2,x3,x4) = alpha in
  let pre =
    if !Config.testnet then
      if p = 0 then 7409 else if p = 1 then 7471 else if p = 2 then 7416 else 7406
    else
      if p = 0 then 58 else if p = 1 then 120 else if p = 2 then 66 else 56
  in
  hashval_gen_addrstr pre (x0,x1,x2,x3,x4)

let fraenks_of_cants v =
  let w = Int64.div v 100000000000L in
  let d = Int64.to_string (Int64.rem v 100000000000L) in
  let dl = String.length d in
  let ez = ref 0 in
  begin
    try
      for i = dl-1 downto 0 do
	if d.[i] = '0' then
	  incr ez
	else
	  raise Exit
      done
    with Exit -> ()
  end;
  let b = Buffer.create 20 in
  Buffer.add_string b (Int64.to_string w);
  Buffer.add_char b '.';
  for i = 1 to 11 - dl do
    Buffer.add_char b '0'
  done;
  for i = 0 to dl - (1 + !ez) do
    Buffer.add_char b d.[i]
  done;
  Buffer.contents b

let cants_of_fraenks s =
  let f = ref 0L in
  let w = ref true in
  let c = ref 0L in
  let d = ref 100000000000L in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    let cc = Char.code s.[!i] in
    incr i;
    if !w then
      if cc = 46 then
	w := false
      else if cc >= 48 && cc < 58 then
	f := Int64.add (Int64.mul !f 10L) (Int64.of_int (cc-48))
      else
	raise (Failure ("cannot interpret " ^ s ^ " as a number of fraenks"))
    else
      if cc >= 48 && cc < 58 then
	begin
	  c := Int64.add !c (Int64.mul !d (Int64.of_int (cc-48)));
	  d := Int64.div !d 10L
	end
      else
	raise (Failure ("cannot interpret " ^ s ^ " as a number of fraenks"))
  done;
  Int64.add (Int64.mul !f 1000000000000L) !c

