(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Ser
open Sha256
open Ripemd160
open Hash
open Secp256k1
open Cryptocurr
open Signat

exception Invalid
exception OP_ELSE of int list * int list list * int list list
exception OP_ENDIF of int list * int list list * int list list

let print_bytelist bl =
  List.iter (fun b -> Printf.printf " %d" b) bl

let print_stack stk =
  List.iter (fun bl ->
    Printf.printf "*";
    print_bytelist bl;
    Printf.printf "\n") stk

let hashval_bytelist h =
  let (h4,h3,h2,h1,h0) = h in
  let bl = ref [] in
  bl := Int32.to_int (Int32.logand h0 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h0 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h0 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h0 24)::!bl;
  bl := Int32.to_int (Int32.logand h1 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h1 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h1 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h1 24)::!bl;
  bl := Int32.to_int (Int32.logand h2 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h2 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h2 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h2 24)::!bl;
  bl := Int32.to_int (Int32.logand h3 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h3 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h3 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h3 24)::!bl;
  bl := Int32.to_int (Int32.logand h4 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h4 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h4 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h4 24)::!bl;
  !bl

let md256_bytelist h =
  let (h7,h6,h5,h4,h3,h2,h1,h0) = h in
  let bl = ref [] in
  bl := Int32.to_int (Int32.logand h0 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h0 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h0 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h0 24)::!bl;
  bl := Int32.to_int (Int32.logand h1 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h1 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h1 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h1 24)::!bl;
  bl := Int32.to_int (Int32.logand h2 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h2 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h2 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h2 24)::!bl;
  bl := Int32.to_int (Int32.logand h3 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h3 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h3 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h3 24)::!bl;
  bl := Int32.to_int (Int32.logand h4 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h4 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h4 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h4 24)::!bl;
  bl := Int32.to_int (Int32.logand h4 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h4 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h4 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h4 24)::!bl;
  bl := Int32.to_int (Int32.logand h5 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h5 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h5 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h5 24)::!bl;
  bl := Int32.to_int (Int32.logand h6 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h6 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h6 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h6 24)::!bl;
  bl := Int32.to_int (Int32.logand h7 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h7 8) 255l)::!bl;
  bl := Int32.to_int (Int32.logand (Int32.shift_right_logical h7 16) 255l)::!bl;
  bl := Int32.to_int (Int32.shift_right_logical h7 24)::!bl;
  !bl

let hash160_bytelist l =
  let b = Buffer.create 100 in
  List.iter (fun x -> Buffer.add_char b (Char.chr x)) l;
  hash160 (Buffer.contents b)

let sha256_bytelist l =
  let b = Buffer.create 100 in
  List.iter (fun x -> Buffer.add_char b (Char.chr x)) l;
  sha256str (Buffer.contents b)

let hash256_bytelist l =
  let b = Buffer.create 100 in
  List.iter (fun x -> Buffer.add_char b (Char.chr x)) l;
  sha256dstr (Buffer.contents b)

let rec next_bytes i bl =
  if i > 0 then
    begin
      match bl with
      | [] -> raise (Failure("missing bytes"))
      | (b::br) ->
	  let (byl,bs) = next_bytes (i-1) br in
	  (b::byl,bs)
    end
  else
    ([],bl)

let rec remove_nth n l =
  match l with
  | (x::r) -> if n = 0 then r else x::remove_nth (n-1) r
  | [] -> raise (Failure("remove_nth called with too big an n or too short a list"))

(*** inum_le and blnum_le are little endian; inum_be and blnum_be are big endian ***)
let rec inumr_le x r s =
  match x with
  | [] -> r
  | (y::z) ->
      inumr_le z (add_big_int r (shift_left_big_int (big_int_of_int y) s)) (s + 8)

let inum_le x =
  inumr_le x zero_big_int 0

let rec inumr_be x r =
  match x with
  | [] -> r
  | (y::z) ->
      inumr_be z (or_big_int (big_int_of_int y) (shift_left_big_int r 8))

let inum_be x =
  inumr_be x zero_big_int

let next_inum_le i bl =
  let (bs,br) = next_bytes i bl in
  (inum_le bs,br)

let next_inum_be i bl =
  let (bs,br) = next_bytes i bl in
  (inum_be bs,br)

let rec blnum_le x i =
  if i > 0 then
    (int_of_big_int (and_big_int x (big_int_of_int 255)))::(blnum_le (shift_right_towards_zero_big_int x 8) (i-1))
  else
    []

let rec blnum_be x i =
  if i > 0 then
    (int_of_big_int (and_big_int (shift_right_towards_zero_big_int x ((i-1)*8)) (big_int_of_int 255)))::(blnum_be x (i-1))
  else
    []

let num32 x =
  let (x0,x1,x2,x3) =
    match x with
    | [x0;x1;x2;x3] -> (x0,x1,x2,x3)
    | [x0;x1;x2] -> (x0,x1,x2,0)
    | [x0;x1] -> (x0,x1,0,0)
    | [x0] -> (x0,0,0,0)
    | [] -> (0,0,0,0)
    | _ -> raise (Failure "not a 32-bit integer")
  in
  Int32.logor (Int32.of_int x0)
    (Int32.logor (Int32.shift_left (Int32.of_int x1) 8)
       (Int32.logor (Int32.shift_left (Int32.of_int x2) 16)
	  (Int32.shift_left (Int32.of_int x2) 24)))

let blnum32 x =
  [Int32.to_int (Int32.logand x 255l);
   Int32.to_int (Int32.logand (Int32.shift_right_logical x 8) 255l);
   Int32.to_int (Int32.logand (Int32.shift_right_logical x 16) 255l);
   Int32.to_int (Int32.logand (Int32.shift_right_logical x 24) 255l)]

(***
 format: 02 x, 03 x or 04 x y,
 ***)
let bytelist_to_pt bl =
  match bl with
  | (z::xl) when z = 2 ->
      let x = inum_be xl in
      Some(x,curve_y true x)
  | (z::xl) when z = 3 ->
      let x = inum_be xl in
      Some(x,curve_y false x)
  | (z::br) when z = 4 ->
      let (xl,yl) = next_bytes 32 br in
      let x = inum_be xl in
      let y = inum_be yl in
      Printf.printf "x: %s\ny: %s\n" (string_of_big_int x) (string_of_big_int y);
      Some(x,y)
  | _ -> None

let rec data_from_stack n stk =
  if n > 0 then
    begin
      match stk with
      | (d::stk2) ->
	  let (data,stkr) = data_from_stack (n-1) stk2 in
	  (d::data,stkr)
      | [] -> raise (Failure("Unexpected case in data_from_stack, not enough items on the stack"))
    end
  else
    ([],stk)

let num_data_from_stack stk =
  match stk with
  | (x::stk) ->
      let n = int_of_big_int (inum_le x) in
      if n >= 0 then
	data_from_stack n stk
      else
	raise (Failure("Neg number in num_data_from_stack"))
  | _ ->
      raise (Failure("Empty stack in num_data_from_stack"))

let inside_ifs = ref 0;;

let rec skip_statements bl stp =
  match bl with
  | [] -> raise (Failure("Ran out of commands before IF block ended"))
  | (b::br) when List.mem b stp -> (b,br)
  | (b::br) when b > 0 && b < 76 ->
      let (byl,bs) = next_bytes b br in
      skip_statements bs stp
  | (76::b::br) ->
      let (byl,bs) = next_bytes b br in
      skip_statements bs stp
  | (77::b0::b1::br) ->
      let (byl,bs) = next_bytes (b0+256*b1) br in
      skip_statements bs stp
  | (78::b0::b1::b2::b3::br) ->
      let (byl,bs) = next_bytes (b0+256*b1+65536*b2+16777216*b3) br in
      skip_statements bs stp
  | (b::br) when b = 99 || b = 100 ->
      let (_,bs) = skip_statements br [104] in
      skip_statements bs stp
  | (b::br) ->
      skip_statements br stp

let rec eval_script (tosign:big_int) bl stk altstk =
  match bl with
  | [] -> (stk,altstk)
  | (0::br) -> eval_script tosign br ([]::stk) altstk
  | (b::br) when b < 76 ->
      let (byl,bs) = next_bytes b br in
      eval_script tosign bs (byl::stk) altstk
  | (76::b::br) ->
      let (byl,bs) = next_bytes b br in
      eval_script tosign bs (byl::stk) altstk
  | (77::b0::b1::br) ->
      let (byl,bs) = next_bytes (b0+256*b1) br in
      eval_script tosign bs (byl::stk) altstk
  | (78::b0::b1::b2::b3::br) ->
      let (byl,bs) = next_bytes (b0+256*b1+65536*b2+16777216*b3) br in
      eval_script tosign bs (byl::stk) altstk
  | (79::br) -> eval_script tosign br ([129]::stk) altstk
  | (81::br) -> eval_script tosign br ([1]::stk) altstk
  | (b::br) when b >= 82 && b <= 96 -> eval_script tosign br ([b-80]::stk) altstk
  | (97::br) -> eval_script tosign br stk altstk
  | (99::br) ->
      begin
	match stk with
	| x::stkr ->
	    let n = inum_le x in
	    if sign_big_int n = 0 then
	      let (b,bl2) = skip_statements br [103;104] in
	      if b = 103 then
		eval_script_if tosign bl2 stkr altstk
	      else if b = 104 then
		eval_script tosign bl2 stkr altstk
	      else
		begin
		  Printf.printf "IF block ended with %d\n" b;
		  raise (Failure("IF block ended improperly"))
		end
	    else
	      eval_script_if tosign br stkr altstk
	| [] -> raise (Failure("Nothing on stack for OP_IF"))
      end
  | (100::br) ->
      begin
	match stk with
	| x::stkr ->
	    let n = inum_le x in
	    if sign_big_int n = 0 then
	      eval_script_if tosign br stkr altstk
	    else
	      let (b,bl2) = skip_statements br [103;104] in
	      if b = 103 then
		eval_script_if tosign bl2 stkr altstk
	      else if b = 104 then
		eval_script tosign bl2 stkr altstk
	      else
		begin
		  Printf.printf "IF block ended with %d\n" b;
		  raise (Failure("IF block ended improperly"))
		end
	| [] -> raise (Failure("Nothing on stack for OP_NOTIF"))
      end
  | (103::br) -> raise (OP_ELSE(br,stk,altstk))
  | (104::br) -> raise (OP_ENDIF(br,stk,altstk))
  | (105::br) ->
      begin
	match stk with
	| ([1]::stkr) -> eval_script tosign br stk altstk
	| _ -> raise Invalid
      end
  | (106::br) -> raise Invalid
  | (107::br) ->
      begin
	match stk with
	| (x::stkr) -> eval_script tosign br stkr (x::altstk)
	| _ -> raise (Failure("not enough inputs to OP_TOALTSTACK"))
      end
  | (108::br) ->
      begin
	match altstk with
	| (x::altstkr) -> eval_script tosign br (x::stk) altstkr
	| _ -> raise (Failure("alt stack empty when OP_FROMALTSTACK occurred"))
      end
  | (109::br) ->
      begin
	match stk with
	| (_::_::stkr) -> eval_script tosign br stkr altstk
	| _ -> raise (Failure("not enough inputs to OP_2DROP"))
      end
  | (110::br) ->
      begin
	match stk with
	| (x2::x1::stkr) -> eval_script tosign br (x2::x1::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_2DUP"))
      end
  | (111::br) ->
      begin
	match stk with
	| (x3::x2::x1::stkr) -> eval_script tosign br (x3::x2::x1::x3::x2::x1::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_3DUP"))
      end
  | (112::br) ->
      begin
	match stk with
	| (x4::x3::x2::x1::stkr) -> eval_script tosign br (x2::x1::x4::x3::x2::x1::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_2OVER"))
      end
  | (113::br) ->
      begin
	match stk with
	| (x6::x5::x4::x3::x2::x1::stkr) -> eval_script tosign br (x2::x1::x6::x5::x4::x3::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_2ROT"))
      end
  | (114::br) ->
      begin
	match stk with
	| (x4::x3::x2::x1::stkr) -> eval_script tosign br (x2::x1::x4::x3::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_2SWAP"))
      end
  | (115::br) ->
      begin
	match stk with
	| ([]::stkr) -> eval_script tosign br stk altstk
	| (x::stkr) -> eval_script tosign br (x::x::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_IFDUP"))
      end
  | (116::br) ->
      let l = Int32.of_int (List.length stk) in
      eval_script tosign br (blnum32 l::stk) altstk
  | (117::br) ->
      begin
	match stk with
	| (_::stkr) -> eval_script tosign br stkr altstk
	| _ -> raise (Failure("not enough inputs to OP_DROP"))
      end
  | (118::br) ->
      begin
	match stk with
	| (x::stkr) -> eval_script tosign br (x::stk) altstk
	| _ -> raise (Failure("not enough inputs to OP_DUP"))
      end
  | (119::br) ->
      begin
	match stk with
	| (x2::x1::stkr) -> eval_script tosign br (x2::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_NIP"))
      end
  | (120::br) ->
      begin
	match stk with
	| (x2::x1::stkr) -> eval_script tosign br (x1::x2::x1::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_OVER"))
      end
  | (121::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = inum_le x in
	    if lt_big_int n zero_big_int then
	      raise (Failure("neg number given in OP_PICK"))
	    else
	      let n = int_of_big_int n in
	      begin
		try
		  let xn = List.nth stkr n in
		  eval_script tosign br (xn::stkr) altstk
		with Failure(z) -> if z = "nth" then raise (Failure("Not enough on stack for OP_PICK")) else raise (Failure(z))
	      end
	| _ -> raise (Failure("not enough inputs for OP_PICK"))
      end
  | (122::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = inum_le x in
	    if lt_big_int n zero_big_int then
	      raise (Failure("neg number given in OP_ROLL"))
	    else
	      let n = int_of_big_int n in
	      begin
		try
		  let xn = List.nth stkr n in
		  eval_script tosign br (xn::remove_nth n stkr) altstk
		with Failure(z) -> if z = "nth" then raise (Failure("Not enough on stack for OP_ROLL")) else raise (Failure(z))
	      end
	| _ -> raise (Failure("not enough inputs for OP_ROLL"))
      end
  | (123::br) ->
      begin
	match stk with
	| (x3::x2::x1::stkr) -> eval_script tosign br (x1::x3::x2::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_ROT"))
      end
  | (124::br) ->
      begin
	match stk with
	| (x2::x1::stkr) -> eval_script tosign br (x1::x2::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_SWAP"))
      end
  | (125::br) ->
      begin
	match stk with
	| (x2::x1::stkr) -> eval_script tosign br (x2::x1::x2::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_TUCK"))
      end
  | (130::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = List.length x in
	    eval_script tosign br (blnum32 (Int32.of_int n)::stk) altstk
	| _ -> raise (Failure("not enough inputs to OP_SIZE"))
      end
  | (135::br) ->
      begin
	match stk with
	| (x::y::stkr) ->
	    if eq_big_int (inum_le x) (inum_le y) then (*** Handling this the same way as OP_NUMEQUAL since there are examples where [] is considered equal to [0]. ***)
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_EQUAL"))
      end
  | (136::br) ->
      begin
	match stk with
	| (x::y::stkr) ->
	    if eq_big_int (inum_le x) (inum_le y) then (*** Handling this the same way as OP_NUMEQUAL since there are examples where [] is considered equal to [0]. ***)
	      eval_script tosign br stkr altstk
	    else
	      raise Invalid
	| _ -> raise (Failure ("not enough inputs for OP_EQUAL"))
      end
  | (139::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = num32 x in
	    eval_script tosign br (blnum32 (Int32.add n 1l)::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_1ADD"))
      end
  | (140::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = num32 x in
	    eval_script tosign br (blnum32 (Int32.sub n 1l)::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_1SUB"))
      end
  | (143::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = num32 x in
	    eval_script tosign br (blnum32 (Int32.neg n)::stk) altstk
	| _ -> raise (Failure("not enough inputs to OP_NEGATE"))
      end
  | (144::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = num32 x in
	    eval_script tosign br (blnum32 (Int32.abs n)::stk) altstk
	| _ -> raise (Failure("not enough inputs to OP_ABS"))
      end
  | (145::br) ->
      begin
        match stk with
        | (x::stkr) ->
           let n = inum_le x in
           if sign_big_int n = 0 then
             eval_script tosign br ([1]::stkr) altstk
           else
             eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_NOT"))
      end
  | (146::br) ->
      begin
	match stk with
	| (x::stkr) ->
           let n = inum_le x in
           if sign_big_int n = 0 then
             eval_script tosign br ([]::stkr) altstk
           else 
             eval_script tosign br ([1]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_0NOTEQUAL"))
      end
  | (147::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    let z = Int32.add (num32 x) (num32 y) in
	    eval_script tosign br (blnum32 z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_ADD"))
      end
  | (148::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    let z = Int32.sub (num32 x) (num32 y) in
	    eval_script tosign br (blnum32 z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_SUB"))
      end
  | (154::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if sign_big_int (inum_le x) = 0 || sign_big_int (inum_le y) = 0 then
	      eval_script tosign br ([]::stkr) altstk
	    else
	      eval_script tosign br ([1]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_BOOLAND"))
      end
  | (155::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if sign_big_int (inum_le x) = 0 && sign_big_int (inum_le y) = 0 then
	      eval_script tosign br ([]::stkr) altstk
	    else
	      eval_script tosign br ([1]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_BOOLOR"))
      end
  | (156::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if eq_big_int (inum_le x) (inum_le y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_NUMEQUAL"))
      end
  | (157::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if eq_big_int (inum_le x) (inum_le y) then
	      eval_script tosign br stkr altstk
	    else
	      raise Invalid
	| _ -> raise (Failure ("not enough inputs for OP_NUMEQUALVERIFY"))
      end
  | (158::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if eq_big_int (inum_le x) (inum_le y) then
	      eval_script tosign br ([]::stkr) altstk
	    else
	      eval_script tosign br ([1]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_NUMNOTEQUAL"))
      end
  | (159::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if lt_big_int (inum_le x) (inum_le y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_LESSTHAN"))
      end
  | (160::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if gt_big_int (inum_le x) (inum_le y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_GREATERTHAN"))
      end
  | (161::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if le_big_int (inum_le x) (inum_le y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_LESSTHANOREQUAL"))
      end
  | (162::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if ge_big_int (inum_le x) (inum_le y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_GREATERTHANOREQUAL"))
      end
  | (163::br) ->
      let min32 x y = if x > y then y else x in
      begin
	match stk with
	| (y::x::stkr) ->
	    let z = min32 (num32 x) (num32 y) in
	    eval_script tosign br (blnum32 z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_MIN"))
      end
  | (164::br) ->
      let max32 x y = if x < y then y else x in
      begin
	match stk with
	| (y::x::stkr) ->
	    let z = max32 (num32 x) (num32 y) in
	    eval_script tosign br (blnum32 z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_MAX"))
      end
  | (165::br) ->
      begin
	match stk with
	| (mx::mn::x::stkr) ->
	    let xx = num32 x in
	    if num32 mn <= xx && xx < (num32 mx) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_WITHIN"))
      end
  | (168::br) ->
      begin
	match stk with
	| (l::stkr) -> eval_script tosign br ((md256_bytelist (sha256_bytelist l))::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for SHA256"))
      end
  | (169::br) ->
      begin
	match stk with
	| (l::stkr) -> eval_script tosign br ((hashval_bytelist (hash160_bytelist l))::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for HASH160"))
      end
  | (170::br) ->
      begin
	match stk with
	| (l::stkr) -> eval_script tosign br ((md256_bytelist (hash256_bytelist l))::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for HASH256"))
      end
  | (172::br) -> (** OP_CHECKSIG, this differs from Bitcoin; the (r,s) are given as 2 32-byte big endian integers and are not DER encoded **)
      begin
	match stk with
	| (pubkey::gsg::stkr) -> eval_script tosign br (if checksig tosign gsg pubkey then ([1]::stkr) else ([]::stkr)) altstk
	| _ -> raise (Failure ("not enough inputs for OP_CHECKSIG"))
      end
  | (173::br) -> (** OP_CHECKSIG_VERIFY, this differs from Bitcoin; the (r,s) are given as 2 32-byte big endian integers and are not DER encoded **)
      begin
	match stk with
	| (pubkey::gsg::stkr) -> if checksig tosign gsg pubkey then eval_script tosign br stkr altstk else raise Invalid
	| _ -> raise (Failure ("not enough inputs for OP_CHECKSIGVERIFY"))
      end
  | (174::br) -> (** OP_CHECK_MULTISIG, this differs from Bitcoin; it doesn't take an extra unused argument; also the (r,s) are given as 2 32-byte big endian integers and are not DER encoded **)
      let (pubkeys,stk2) = num_data_from_stack stk in
      let (gsgs,stk3) = num_data_from_stack stk2 in
      eval_script tosign br (if checkmultisig tosign gsgs pubkeys then ([1]::stk3) else ([]::stk3)) altstk
  | (175::br) -> (** OP_CHECK_MULTISIG_VERIFY, this differs from Bitcoin; it doesn't take an extra unused argument; also the (r,s) are given as 2 32-byte big endian integers and are not DER encoded **)
      let (pubkeys,stk2) = num_data_from_stack stk in
      let (gsgs,stk3) = num_data_from_stack stk2 in
      if checkmultisig tosign gsgs pubkeys then eval_script tosign br stk3 altstk else raise Invalid
  | (171::br) -> eval_script tosign br stk altstk (** treat OP_CODESEPARATOR as a no op **)
  | (b::br) when b = 97 || b >= 176 && b <= 185 -> eval_script tosign br stk altstk (** no ops **)
  | (80::br) ->
      if !inside_ifs > 0 then
	eval_script tosign br stk altstk
      else
	raise Invalid
  | _ ->
      print_bytelist bl;
      raise (Failure ("Unhandled case"))
and eval_script_if tosign bl stk allstk =
  try
    incr inside_ifs;
    eval_script tosign bl stk allstk
  with
  | OP_ELSE(br,stk2,allstk2) ->
      let (b,br2) = skip_statements br [103;104] in
      if b = 103 then
	eval_script_if tosign br2 stk2 allstk2
      else if b = 104 then
	begin
	  decr inside_ifs;
	  eval_script tosign br2 stk2 allstk2
	end
      else
	begin
	  Printf.printf "IF block ended with %d\n" b;
	  raise (Failure("IF block ended improperly"))
	end	
  | OP_ENDIF(br,stk2,allstk2) ->
      decr inside_ifs;
      eval_script tosign br stk2 allstk2

(*** eval_script is mutually recursive with checksig and checkmultisig since endorsements require scripts to be evaluated to check the signatures of endorsees ***)
and checksig tosign gsg pubkey =
  try
    let q = bytelist_to_pt pubkey in
    match gsg with
    | (z::rsl) when z = 0 -> (*** ordinary signature: 0 <r[32 bytes]> <s[32 bytes]> ***)
	let (r,sbl) = next_inum_be 32 rsl in
	let s = inum_be sbl in
	verify_signed_big_int tosign q (r,s)
    | (z::esg) when z = 1 -> (*** signature via endorsement of a p2pkh to p2pkh: 1 <r[32 bytes]> <s[32 bytes]> <r2[32 bytes]> <s2[32 bytes]> <compr_or_uncompr_byte> <pubkey2> ***)
	let (r,esg) = next_inum_be 32 esg in
	let (s,esg) = next_inum_be 32 esg in
	let (r2,esg) = next_inum_be 32 esg in
	let (s2,esg) = next_inum_be 32 esg in
	begin
	  match esg with
	  | (c::esg) ->
	      let q2 = bytelist_to_pt (c::esg) in
	      begin
		match q2 with
		| Some(x2,y2) ->
		    let x2m = big_int_md256 x2 in
		    let beta =
		      if c = 4 then
			let y2m = big_int_md256 y2 in
			hashpubkey x2m y2m
		      else
			hashpubkeyc c x2m
		    in
		    (*** alpha signs that beta can sign ***)
		    let ee = md256_big_int (md256_of_bitcoin_message ("endorse " ^ (addr_qedaddrstr (hashval_p2pkh_addr beta)))) in
		    verify_signed_big_int ee q (r,s) && verify_signed_big_int tosign q2 (r2,s2)
		| None -> false
	      end
	  | _ -> false
	end
    | (z::esg) when z = 2 -> (*** signature via endorsement of a p2pkh to p2sh: 2 <20 byte p2sh address beta> <r[32 bytes]> <s[32 bytes]> <script> ***)
	let (betal,esg) = next_bytes 20 esg in
	let beta =  big_int_hashval (inum_be betal) in
	let (r,esg) = next_inum_be 32 esg in
	let (s,scr2) = next_inum_be 32 esg in
	(*** alpha signs that beta can sign ***)
	let ee = md256_big_int (md256_of_bitcoin_message ("endorse " ^ (addr_qedaddrstr (hashval_p2sh_addr beta)))) in
	verify_signed_big_int ee q (r,s) && check_p2sh tosign beta scr2
    | _ -> false
  with Failure(x) -> false

(*** eval_script is mutually recursive with checksig and checkmultisig since endorsements require scripts to be evaluated to check the signatures of endorsees ***)
and checkmultisig tosign gsgs pubkeys =
  match gsgs with
  | [] -> true
  | gsg::gsr ->
      match pubkeys with
      | [] -> false
      | pubkey::pubkeyr ->
	  if checksig tosign gsg pubkey then
	    checkmultisig tosign gsr pubkeyr
	  else
	    checkmultisig tosign gsgs pubkeyr

(*** check_p2sh is mutually recursive with checksig and checkmultisig since endorsements require scripts to be evaluated to check the signatures of endorsees ***)
and check_p2sh (tosign:big_int) h s =
  let (stk,altstk) = eval_script tosign s [] [] in
  match stk with
  | [] -> false
  | (s1::stkr) ->
      if h = hash160_bytelist s1 then
	begin
	  let (stk2,_) = eval_script tosign s1 stkr altstk in
	  match stk2 with
	  | [] -> false
	  | (x::_) ->
	      if eq_big_int (inum_le x) zero_big_int then
		false
	      else
		true
	end
      else
	begin
	  false
	end

(*** This version catches all exceptions and returns false. It should be called by all outside functions ***)
let verify_p2sh tosign beta scr =
  try
    check_p2sh tosign beta scr
  with
  | _ -> false

(*** Generalized Signatures ***)
type gensignat =
  | P2pkhSignat of pt * bool * signat
  | P2shSignat of int list
  | EndP2pkhToP2pkhSignat of pt * bool * pt * bool * signat * signat
  | EndP2pkhToP2shSignat of pt * bool * hashval * signat * int list
  | EndP2shToP2pkhSignat of pt * bool * int list * signat
  | EndP2shToP2shSignat of hashval * int list * int list

let verify_gensignat e gsg alpha =
  match gsg with
  | P2pkhSignat(Some(x,y),c,sg) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 0 then (* p2pkh *)
	let xm = big_int_md256 x in
	let ym = big_int_md256 y in
	let alpha2 = if c then (if evenp y then hashpubkeyc 2 xm else hashpubkeyc 3 xm) else hashpubkey xm ym in
	(x0,x1,x2,x3,x4) = alpha2 && verify_signed_big_int e (Some(x,y)) sg
      else
	false
  | P2shSignat(scr) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 0 then (* p2sh *)
	verify_p2sh e (x0,x1,x2,x3,x4) scr
      else
	false
  | EndP2pkhToP2pkhSignat(Some(x,y),c,Some(w,z),d,esg,sg) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 0 then (* p2pkh *)
	let xm = big_int_md256 x in
	let ym = big_int_md256 y in
	let wm = big_int_md256 w in
	let zm = big_int_md256 z in
	let alpha2 = if c then (if evenp y then hashpubkeyc 2 xm else hashpubkeyc 3 xm) else hashpubkey xm ym in
	let beta = if d then (if evenp z then hashpubkeyc 2 wm else hashpubkeyc 3 wm) else hashpubkey wm zm in
	let ee = md256_big_int (md256_of_bitcoin_message ("endorse " ^ (addr_qedaddrstr (hashval_p2pkh_addr beta)))) in
	(x0,x1,x2,x3,x4) = alpha2 && verify_signed_big_int ee (Some(x,y)) esg && verify_signed_big_int e (Some(w,z)) sg
      else
	false
  | EndP2pkhToP2shSignat(Some(x,y),c,beta,esg,scr) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 0 then (* p2pkh *)
	let xm = big_int_md256 x in
	let ym = big_int_md256 y in
	let alpha2 = if c then (if evenp y then hashpubkeyc 2 xm else hashpubkeyc 3 xm) else hashpubkey xm ym in
	let ee = md256_big_int (md256_of_bitcoin_message ("endorse " ^ (addr_qedaddrstr (hashval_p2sh_addr beta)))) in
	(x0,x1,x2,x3,x4) = alpha2 && verify_signed_big_int ee (Some(x,y)) esg && verify_p2sh e beta scr
      else
	false
  | EndP2shToP2pkhSignat(Some(w,z),d,escr,sg) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 1 then (* p2sh *)
	let wm = big_int_md256 w in
	let zm = big_int_md256 z in
	let beta = if d then (if evenp z then hashpubkeyc 2 wm else hashpubkeyc 3 wm) else hashpubkey wm zm in
	let ee = md256_big_int (md256_of_bitcoin_message ("endorse " ^ (addr_qedaddrstr (hashval_p2pkh_addr beta)))) in
	verify_p2sh ee (x0,x1,x2,x3,x4) escr && verify_signed_big_int e (Some(w,z)) sg
      else
	false
  | EndP2shToP2shSignat(beta,escr,scr) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 1 then (* p2sh *)
	let ee = md256_big_int (md256_of_bitcoin_message ("endorse " ^ (addr_qedaddrstr (hashval_p2sh_addr beta)))) in
	verify_p2sh ee (x0,x1,x2,x3,x4) escr && verify_p2sh e beta scr
      else
	false
  | _ -> false
  
let seo_gensignat o gsg c =
  match gsg with
  | P2pkhSignat(p,b,sg) -> (* 00 *)
      let c = o 2 0 c in
      seo_prod3 seo_pt seo_bool seo_signat o (p,b,sg) c
  | P2shSignat(scr) -> (* 01 *)
      let c = o 2 1 c in
      seo_list seo_int8 o scr c
  | EndP2pkhToP2pkhSignat(p,b,q,d,esg,sg) -> (* 10 0 *)
      let c = o 3 2 c in
      seo_prod6 seo_pt seo_bool seo_pt seo_bool seo_signat seo_signat o (p,b,q,d,esg,sg) c
  | EndP2pkhToP2shSignat(p,b,beta,esg,scr) -> (* 10 1 *)
      let c = o 3 6 c in
      seo_prod5 seo_pt seo_bool seo_hashval seo_signat (seo_list seo_int8) o (p,b,beta,esg,scr) c
  | EndP2shToP2pkhSignat(q,d,escr,sg) -> (* 11 0 *)
      let c = o 3 3 c in
      seo_prod4 seo_pt seo_bool (seo_list seo_int8) seo_signat o (q,d,escr,sg) c
  | EndP2shToP2shSignat(beta,escr,scr) -> (* 11 1 *)
      let c = o 3 7 c in
      seo_prod3 seo_hashval (seo_list seo_int8) (seo_list seo_int8) o (beta,escr,scr) c

let sei_gensignat i c =
  let (x,c) = i 2 c in
  if x = 0 then
    let ((p,b,sg),c) = sei_prod3 sei_pt sei_bool sei_signat i c in
    (P2pkhSignat(p,b,sg),c)
  else if x = 1 then
    let (scr,c) = sei_list sei_int8 i c in
    (P2shSignat(scr),c)
  else if x = 2 then
    let (x,c) = i 1 c in
    if x = 0 then
      let ((p,b,q,d,esg,sg),c) = sei_prod6 sei_pt sei_bool sei_pt sei_bool sei_signat sei_signat i c in
      (EndP2pkhToP2pkhSignat(p,b,q,d,esg,sg),c)
    else
      let ((p,b,beta,esg,scr),c) = sei_prod5 sei_pt sei_bool sei_hashval sei_signat (sei_list sei_int8) i c in
      (EndP2pkhToP2shSignat(p,b,beta,esg,scr),c)
  else
    let (x,c) = i 1 c in
    if x = 0 then
      let ((q,d,escr,sg),c) = sei_prod4 sei_pt sei_bool (sei_list sei_int8) sei_signat i c in
      (EndP2shToP2pkhSignat(q,d,escr,sg),c)
    else
      let ((beta,escr,scr),c) = sei_prod3 sei_hashval (sei_list sei_int8) (sei_list sei_int8) i c in
      (EndP2shToP2shSignat(beta,escr,scr),c)
