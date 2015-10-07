(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Net;;
open Setconfig;;
open Commands;;

process_config_args();;
process_config_file();;

let build_rpccall r =
  match r with
  | [c] when c = "stop" ->
      (Stop,fun i -> ())
  | [c;n] when c = "addnode" ->
      (AddNode(n),
       fun i ->
	 let by = input_byte i in
	 if by = 0 then
	   Printf.printf "Node not added.\n"
	 else
	   Printf.printf "Node added.\n"
      )
  | [c] when c = "getinfo" ->
      (GetInfo,
       fun i ->
	 let s = rec_string i in
	 output_string stdout s)
  | [c;a] when c = "importwatchaddr" ->
      (ImportWatchAddr(a),
       fun i ->
	 let by = input_byte i in
	 if by = 0 then
	   begin
	     Printf.printf "Watch address not added:\n";
	     let s = rec_string i in
	     Printf.printf "%s\n" s;
	   end
	 else
	   Printf.printf "Watch address added.\n")
  | [c;k] when c = "importprivkey" ->
      (ImportPrivKey(k),
       fun i ->
	 let by = input_byte i in
	 let s = rec_string i in
	 if by = 0 then
	   begin
	     Printf.printf "Private key not added.\n";
	     Printf.printf "%s\n" s;
	   end
	 else
	   Printf.printf "Private key for address %s added.\n" s
      )
  | [c;a] when c = "importwatchbtcaddr" ->
      (ImportWatchBtcAddr(a),
       fun i ->
	 let by = input_byte i in
	 let s = rec_string i in
	 if by = 0 then
	   begin
	     Printf.printf "Watch address not added:\n";
	     Printf.printf "%s\n" s;
	   end
	 else
	   Printf.printf "Watch address %s added.\n" s)
  | [c;k] when c = "importbtcprivkey" ->
      (ImportBtcPrivKey(k),
       fun i ->
	 let by = input_byte i in
	 let s = rec_string i in
	 if by = 0 then
	   begin
	     Printf.printf "Private key not added.\n";
	     Printf.printf "%s\n" s;
	   end
	 else
	   Printf.printf "Private key for address %s added.\n" s
      )
  | [c;scr] when c = "importp2sh" ->
      (ImportP2sh(scr),
       fun i ->
	 let by = input_byte i in
	 let s = rec_string i in
	 if by = 0 then
	   begin
	     Printf.printf "P2sh script not imported:\n";
	     Printf.printf "%s\n" s;
	   end
	 else
	   Printf.printf "Script for %s imported.\n" s)
  | [c;a;b;s] when c = "importendorsement" ->
      (ImportEndorsement(a,b,s),
       fun i ->
	 let by = input_byte i in
	 if by = 0 then
	   begin
	     Printf.printf "Endorsement not added:\n";
	     let s = rec_string i in
	     Printf.printf "%s\n" s;
	   end
	 else
	   Printf.printf "Endorsement added.\n")
  | (c::_) -> 
      Printf.printf "Unknown rpc command %s.\n" c;
      raise (Failure "Unknown rpc command")
  | [] ->
      Printf.printf "No rpc command was given.\n";
      raise (Failure "Missing rpc command");;

let process_rpccall r f =
  ();;
(***
  try
    let (s,si,so) = connectlocal !Config.rpcport in
    send_rpccom so r;
    begin
      try
	f si
      with
      | End_of_file -> Printf.printf "Response to call was cut off.\n"; flush stdout
    end;
    Unix.close s
  with
  | Unix.Unix_error(Unix.ECONNREFUSED,m1,m2) when m1 = "connect" && m2 = "" ->
      Printf.printf "Could not connect to Qeditas rpc server.\nConnection refused.\n"
  | Unix.Unix_error(Unix.ECONNREFUSED,m1,m2) ->
      Printf.printf "Could not connect to Qeditas rpc server.\nConnection refused. %s; %s\n" m1 m2;
  | Unix.Unix_error(_,m1,m2) ->
      Printf.printf "Could not connect to Qeditas rpc server.\n%s; %s\n" m1 m2;;
***)

let a = Array.length Sys.argv;;
let rpccallr = ref [];;
let rpcstarted = ref false;;
for i = 1 to a-1 do
  let arg = Sys.argv.(i) in
  if !rpcstarted then
    rpccallr := arg::!rpccallr
  else if not (String.length arg > 1 && arg.[0] = '-') then
    begin
      rpcstarted := true;
      rpccallr := [arg]
    end
done;;
let (r,f) = build_rpccall (List.rev !rpccallr);;
process_rpccall r f;;
