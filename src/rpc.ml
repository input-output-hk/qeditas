(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Config
open Ser
open Net
  
type rpccom =
    Stop
  | AddNode of string

let send_string c x =
  let l = String.length x in
  let c2 = seo_varint seoc (Int64.of_int l) (c,None) in
  seocf c2;
  for i = 0 to l-1 do
    output_byte c (Char.code x.[i])
  done

let rec_string c =
  let (l64,_) = sei_varint seic (c,None) in
  let l = Int64.to_int l64 in
  let x = Buffer.create l in
  for i = 0 to l-1 do
    let b = input_byte c in
    Buffer.add_char x (Char.chr b)
  done;
  Buffer.contents x

let send_rpccom c r =
  begin
    match r with
    | Stop ->
	output_byte c 0
    | AddNode(n) ->
	output_byte c 1;
	send_string c n
    | _ -> ()
  end;
  flush c

let rec_rpccom c =
  let by0 = input_byte c in
  match by0 with
  | 0 -> Stop
  | 1 ->
      let n = rec_string c in
      AddNode(n)
  | _ -> raise (Failure "Unknown rpc command")

let addnode remip remport =
  match !socks with
  | None -> (*** no proxy ***)
      begin
	try
	  let (r,ri,ro) = connectpeer remip remport in
	  true
	with _ ->
	  false
      end
  | Some(s) when s = 4 -> (*** socks4 ***)
      begin
	try
	  let (r,ri,ro) = connectpeer_socks4 !socksport remip remport in
	  true
	with _ -> false
      end
  | Some(s) when s = 5 -> (*** socks5, not yet implemented ***)
      false
  | _ -> (*** unknown ***)
      false

let do_rpccom r c =
  match r with
  | AddNode(n) ->
      let (remip,remport) = extract_ip_and_port n in
      if addnode remip remport then
	output_byte c 1
      else
	output_byte c 0
  | _ -> ()

