(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
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

(*** inum and blnum are little endian ***)
let rec inumr x r s =
  match x with
  | [] -> r
  | [y] ->
      if y >= 128 then
	minus_big_int (add_big_int r (shift_left_big_int (big_int_of_int (y land 127)) s))
      else
	add_big_int r (shift_left_big_int (big_int_of_int y) s)
  | (y::z) ->
      inumr z (add_big_int r (shift_left_big_int (big_int_of_int y) s)) (s + 8)

let inum x = inumr x zero_big_int 0

let rec blnumr x p r =
  if gt_big_int x zero_big_int then
    if gt_big_int x (big_int_of_int 255) then
      blnumr (shift_right_towards_zero_big_int x 8) p (int_of_big_int (and_big_int x (big_int_of_int 255))::r)
    else
      let xx = int_of_big_int x in
      if xx > 127 && not p then
	(128::xx::r)
      else if not p then
	(128 lor xx::r)
      else
	(xx::r)
  else
    r
      
let blnum x =
  match sign_big_int x with
  | 0 -> []
  | 1 -> List.rev (blnumr x true [])
  | _ -> List.rev (blnumr (minus_big_int x) false [])

let next_inum x =
  match x with
  | (l::r) ->
      let (y,s) = next_bytes l r in
      (inum y,s)
  | _ -> raise (Failure "format problem, next_inum expected leading byte to give length of following number")

(*** format:
  empty for Null point (which presumably never happens since it's not a public key)
  <1 byte giving length of x> <x (little endian)> <y (little endian)> ***)
let bytelist_to_pt bl =
  match bl with
  | (_::_) ->
      let (x,yl) = next_inum bl in
      Some(x,inum yl)
  | [] -> None

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
      let n = int_of_big_int (inum x) in
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
	    let n = inum x in
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
	    let n = inum x in
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
      let l = big_int_of_int (List.length stk) in
      eval_script tosign br (blnum l::stk) altstk
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
	    let n = inum x in
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
	    let n = inum x in
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
	    eval_script tosign br (blnum (big_int_of_int n)::stk) altstk
	| _ -> raise (Failure("not enough inputs to OP_SIZE"))
      end
  | (135::br) ->
      begin
	match stk with
	| (x::y::stkr) ->
	    if eq_big_int (inum x) (inum y) then (*** Handling this the same way as OP_NUMEQUAL since there are examples where [] is considered equal to [0]. ***)
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_EQUAL"))
      end
  | (136::br) ->
      begin
	match stk with
	| (x::y::stkr) ->
	    if eq_big_int (inum x) (inum y) then (*** Handling this the same way as OP_NUMEQUAL since there are examples where [] is considered equal to [0]. ***)
	      eval_script tosign br stkr altstk
	    else
	      raise Invalid
	| _ -> raise (Failure ("not enough inputs for OP_EQUAL"))
      end
  | (139::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = inum x in
	    eval_script tosign br (blnum (succ_big_int n)::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_1ADD"))
      end
  | (140::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = inum x in
	    eval_script tosign br (blnum (pred_big_int n)::stkr) altstk
	| _ -> raise (Failure("not enough inputs to OP_1SUB"))
      end
  | (143::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = inum x in
	    eval_script tosign br (blnum (minus_big_int n)::stk) altstk
	| _ -> raise (Failure("not enough inputs to OP_NEGATE"))
      end
  | (144::br) ->
      begin
	match stk with
	| (x::stkr) ->
	    let n = inum x in
	    eval_script tosign br (blnum (abs_big_int n)::stk) altstk
	| _ -> raise (Failure("not enough inputs to OP_ABS"))
      end
  | (145::br) ->
      begin
        match stk with
        | (x::stkr) ->
           let n = inum x in
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
           let n = inum x in
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
	    let z = add_big_int (inum x) (inum y) in
	    eval_script tosign br (blnum z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_ADD"))
      end
  | (148::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    let z = sub_big_int (inum x) (inum y) in
	    eval_script tosign br (blnum z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_SUB"))
      end
  | (154::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if sign_big_int (inum x) = 0 || sign_big_int (inum y) = 0 then
	      eval_script tosign br ([]::stkr) altstk
	    else
	      eval_script tosign br ([1]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_BOOLAND"))
      end
  | (155::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if sign_big_int (inum x) = 0 && sign_big_int (inum y) = 0 then
	      eval_script tosign br ([]::stkr) altstk
	    else
	      eval_script tosign br ([1]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_BOOLOR"))
      end
  | (156::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if eq_big_int (inum x) (inum y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_NUMEQUAL"))
      end
  | (157::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if eq_big_int (inum x) (inum y) then
	      eval_script tosign br stkr altstk
	    else
	      raise Invalid
	| _ -> raise (Failure ("not enough inputs for OP_NUMEQUALVERIFY"))
      end
  | (158::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if eq_big_int (inum x) (inum y) then
	      eval_script tosign br ([]::stkr) altstk
	    else
	      eval_script tosign br ([1]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_NUMNOTEQUAL"))
      end
  | (159::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if lt_big_int (inum x) (inum y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_LESSTHAN"))
      end
  | (160::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if gt_big_int (inum x) (inum y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_GREATERTHAN"))
      end
  | (161::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if le_big_int (inum x) (inum y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_LESSTHANOREQUAL"))
      end
  | (162::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    if ge_big_int (inum x) (inum y) then
	      eval_script tosign br ([1]::stkr) altstk
	    else
	      eval_script tosign br ([]::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_GREATERTHANOREQUAL"))
      end
  | (163::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    let z = min_big_int (inum x) (inum y) in
	    eval_script tosign br (blnum z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_MIN"))
      end
  | (164::br) ->
      begin
	match stk with
	| (y::x::stkr) ->
	    let z = max_big_int (inum x) (inum y) in
	    eval_script tosign br (blnum z::stkr) altstk
	| _ -> raise (Failure ("not enough inputs for OP_MAX"))
      end
  | (165::br) ->
      begin
	match stk with
	| (mx::mn::x::stkr) ->
	    let xx = inum x in
	    if le_big_int (inum mn) xx && lt_big_int xx (inum mx) then
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
  | (172::br) ->
      begin
	match stk with
	| (pubkey::gsg::stkr) -> eval_script tosign br (if checksig tosign gsg pubkey then ([1]::stkr) else ([]::stkr)) altstk
	| _ -> raise (Failure ("not enough inputs for OP_CHECKSIG"))
      end
  | (173::br) ->
      begin
	match stk with
	| (pubkey::gsg::stkr) -> if checksig tosign gsg pubkey then eval_script tosign br stkr altstk else raise Invalid
	| _ -> raise (Failure ("not enough inputs for OP_CHECKSIGVERIFY"))
      end
  | (174::br) ->
      let (pubkeys,stk2) = num_data_from_stack stk in
      let (gsgs,stk3) = num_data_from_stack stk2 in
      begin
	match stk3 with
	| (_::stk4) -> eval_script tosign br (if checkmultisig tosign gsgs pubkeys then ([1]::stk4) else ([]::stk4)) altstk
	| [] -> raise (Failure ("missing the last (unused) input for CHECK_MULTISIG"))
      end
  | (175::br) ->
      let (pubkeys,stk2) = num_data_from_stack stk in
      let (gsgs,stk3) = num_data_from_stack stk2 in
      begin
	match stk3 with
	| (_::stk4) -> if checkmultisig tosign gsgs pubkeys then eval_script tosign br stk4 altstk else raise Invalid
	| [] -> raise (Failure ("missing the last (unused) input for CHECK_MULTISIGVERIFY"))
      end
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
    | (0::rsl) -> (*** ordinary signature: 0 <len of r in bytes> <r> <s> ***)
	let (r,sbl) = next_inum rsl in
	let s = inum sbl in
	verify_signed_big_int tosign q (r,s)
    | (1::esg) -> (*** signature via endorsement of a p2kh to p2kh: 1 <len of r in bytes> <r> <len of s in bytes> <s> <len of r2 in bytes> <r2> <len of s2> <s2> <compr_or_uncompr_byte> <pubkey2> ***)
	let (r,esg) = next_inum esg in
	let (s,esg) = next_inum esg in
	let (r2,esg) = next_inum esg in
	let (s2,esg) = next_inum esg in
	begin
	  match esg with
	  | (c::esg) when c < 2 ->
	      let q2 = bytelist_to_pt esg in
	      begin
		match q2 with
		| Some(x2,y2) ->
		    let x2m = big_int_md256 x2 in
		    let y2m = big_int_md256 y2 in
		    let beta =
		      if c = 0 then
			hashpubkey x2m y2m
		      else
			hashpubkeyc (if (evenp y2) then 2 else 3) x2m
		    in
		    (*** alpha signs that beta can sign ***)
		    let ee = md256_big_int (md256_of_bitcoin_message ("Qeditas endorsement " ^ (addr_qedaddrstr (hashval_p2pkh_addr beta)))) in
		    verify_signed_big_int ee q (r,s) && verify_signed_big_int tosign q2 (r2,s2)
		| None -> false
	      end
	  | _ -> false
	end
    | (2::esg) -> (*** signature via endorsement of a p2kh to p2sh: 2 <20 byte p2sh address beta> <len of r in bytes> <r> <len of s in bytes> <s> <script> ***)
	let (betal,esg) = next_bytes 20 esg in
	let beta =  big_int_hashval (inum betal) in
	begin
	  match esg with
	  | (by0::esg) ->
	      let (r,esg) = next_inum esg in
	      let (s,scr2) = next_inum esg in
	      (*** alpha signs that beta can sign ***)
	      let ee = md256_big_int (md256_of_bitcoin_message ("Qeditas endorsement " ^ (addr_qedaddrstr (hashval_p2sh_addr beta)))) in
	      verify_signed_big_int ee q (r,s) && check_p2sh tosign beta scr2
	  | [] -> false
	end
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
	      if eq_big_int (inum x) zero_big_int then
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
	let ee = md256_big_int (md256_of_bitcoin_message ("Qeditas endorsement " ^ (addr_qedaddrstr (hashval_p2pkh_addr beta)))) in
	(x0,x1,x2,x3,x4) = alpha2 && verify_signed_big_int ee (Some(x,y)) esg && verify_signed_big_int e (Some(w,z)) sg
      else
	false
  | EndP2pkhToP2shSignat(Some(x,y),c,beta,esg,scr) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 0 then (* p2pkh *)
	let xm = big_int_md256 x in
	let ym = big_int_md256 y in
	let alpha2 = if c then (if evenp y then hashpubkeyc 2 xm else hashpubkeyc 3 xm) else hashpubkey xm ym in
	let ee = md256_big_int (md256_of_bitcoin_message ("Qeditas endorsement " ^ (addr_qedaddrstr (hashval_p2sh_addr beta)))) in
	(x0,x1,x2,x3,x4) = alpha2 && verify_signed_big_int ee (Some(x,y)) esg && verify_p2sh e beta scr
      else
	false
  | EndP2shToP2pkhSignat(Some(w,z),d,escr,sg) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 1 then (* p2sh *)
	let wm = big_int_md256 w in
	let zm = big_int_md256 z in
	let beta = if d then (if evenp z then hashpubkeyc 2 wm else hashpubkeyc 3 wm) else hashpubkey wm zm in
	let ee = md256_big_int (md256_of_bitcoin_message ("Qeditas endorsement " ^ (addr_qedaddrstr (hashval_p2pkh_addr beta)))) in
	verify_p2sh ee (x0,x1,x2,x3,x4) escr && verify_signed_big_int e (Some(w,z)) sg
      else
	false
  | EndP2shToP2shSignat(beta,escr,scr) ->
      let (i,x0,x1,x2,x3,x4) = alpha in
      if i = 1 then (* p2sh *)
	let ee = md256_big_int (md256_of_bitcoin_message ("Qeditas endorsement " ^ (addr_qedaddrstr (hashval_p2sh_addr beta)))) in
	verify_p2sh ee (x0,x1,x2,x3,x4) escr && verify_p2sh e beta scr
      else
	false
  | _ -> false
  
