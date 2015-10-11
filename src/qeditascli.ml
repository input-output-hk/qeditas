(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Net;;
open Setconfig;;
open Commands;;

process_config_args();;
process_config_file();;

let process_command r =
  match r with
(***
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
***)
  | [c] when c = "printassets" ->
      read_wallet();
      printassets()
  | [c;w] when c = "importprivkey" ->
      read_wallet();
      importprivkey w
  | [c;w] when c = "importbtcprivkey" ->
      read_wallet();
      importbtcprivkey w
(***
  | [c;a] when c = "importwatchaddr" ->
      Printf.printf "To do\n"
  | [c;a] when c = "importwatchbtcaddr" ->
      Printf.printf "To do\n"
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
***)
  | (c::_) -> 
      Printf.printf "Unknown command %s.\n" c;
      raise (Failure "Unknown command")
  | [] ->
      Printf.printf "No command was given.\n";
      raise (Failure "Missing command");;

let a = Array.length Sys.argv;;
let commandr = ref [];;
let commstarted = ref false;;
for i = 1 to a-1 do
  let arg = Sys.argv.(i) in
  if !commstarted then
    commandr := arg::!commandr
  else if not (String.length arg > 1 && arg.[0] = '-') then
    begin
      commstarted := true;
      commandr := [arg]
    end
done;;
process_command (List.rev !commandr);;
