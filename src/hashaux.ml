(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int

let hexchar i =
  match i with
  | 0l -> '0'
  | 1l -> '1'
  | 2l -> '2'
  | 3l -> '3'
  | 4l -> '4'
  | 5l -> '5'
  | 6l -> '6'
  | 7l -> '7'
  | 8l -> '8'
  | 9l -> '9'
  | 10l -> 'A'
  | 11l -> 'B'
  | 12l -> 'C'
  | 13l -> 'D'
  | 14l -> 'E'
  | 15l -> 'F'
  | _ -> raise (Failure("Not a hexit"))

let hexchar_inv x =
  match x with
  | '0' -> 0l
  | '1' -> 1l
  | '2' -> 2l
  | '3' -> 3l
  | '4' -> 4l
  | '5' -> 5l
  | '6' -> 6l
  | '7' -> 7l
  | '8' -> 8l
  | '9' -> 9l
  | 'A' -> 10l
  | 'B' -> 11l
  | 'C' -> 12l
  | 'D' -> 13l
  | 'E' -> 14l
  | 'F' -> 15l
  | 'a' -> 10l
  | 'b' -> 11l
  | 'c' -> 12l
  | 'd' -> 13l
  | 'e' -> 14l
  | 'f' -> 15l
  | _ -> raise (Failure("not a hexit: " ^ (string_of_int (Char.code x))))

let hexsubstring_int32 h i =
  Int32.logor (Int32.shift_left (hexchar_inv h.[i]) 28)
    (Int32.logor (Int32.shift_left (hexchar_inv h.[i+1]) 24)
       (Int32.logor (Int32.shift_left (hexchar_inv h.[i+2]) 20)
	  (Int32.logor (Int32.shift_left (hexchar_inv h.[i+3]) 16)
	     (Int32.logor (Int32.shift_left (hexchar_inv h.[i+4]) 12)
		(Int32.logor (Int32.shift_left (hexchar_inv h.[i+5]) 8)
		   (Int32.logor (Int32.shift_left (hexchar_inv h.[i+6]) 4)
		      (hexchar_inv h.[i+7])))))))
  
let int32_hexstring b x =
  Buffer.add_char b (hexchar (Int32.shift_right_logical x 28));
  Buffer.add_char b (hexchar (Int32.logand (Int32.shift_right_logical x 24) 15l));
  Buffer.add_char b (hexchar (Int32.logand (Int32.shift_right_logical x 20) 15l));
  Buffer.add_char b (hexchar (Int32.logand (Int32.shift_right_logical x 16) 15l));
  Buffer.add_char b (hexchar (Int32.logand (Int32.shift_right_logical x 12) 15l));
  Buffer.add_char b (hexchar (Int32.logand (Int32.shift_right_logical x 8) 15l));
  Buffer.add_char b (hexchar (Int32.logand (Int32.shift_right_logical x 4) 15l));
  Buffer.add_char b (hexchar (Int32.logand x 15l))

let big_int_sub_int32 x i =
  Int32.logor
    (Int32.shift_left (int32_of_big_int (and_big_int (shift_right_towards_zero_big_int x (i+16)) (big_int_of_string "65535"))) 16)
    (int32_of_big_int (and_big_int (shift_right_towards_zero_big_int x i) (big_int_of_string "65535")))

let int32_big_int_bits x i =
  or_big_int
    (shift_left_big_int (big_int_of_int32 (Int32.shift_right_logical x 16)) (i+16))
    (shift_left_big_int (big_int_of_int32 (Int32.logand x 65535l)) i)

let int32_rev x =
  Int32.logor
    (Int32.shift_left (Int32.logand x 0xffl) 24)
    (Int32.logor
       (Int32.shift_left (Int32.logand (Int32.shift_right_logical x 8) 0xffl) 16)
       (Int32.logor
	  (Int32.shift_left (Int32.logand (Int32.shift_right_logical x 16) 0xffl) 8)
	  (Int32.logand (Int32.shift_right_logical x 24) 0xffl)))
