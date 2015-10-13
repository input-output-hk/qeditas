(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ctre;;
open Net;;
open Setconfig;;
open Commands;;

process_config_args();;
process_config_file();;

let bitstr_bitseq s =
  let l = String.length s in
  let bl = ref [] in
  for i = l-1 downto 0 do
    if s.[i] = '0' then
      bl := false::!bl
    else if s.[i] = '1' then
      bl := true::!bl
    else
      raise (Failure "illegal character in bit sequence string")
  done;
  !bl

let bitseq_bitstr bl =
  let sb = Buffer.create 20 in
  List.iter (fun b -> Buffer.add_char sb (if b then '1' else '0')) bl;
  Buffer.contents sb

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
      load_wallet();
      printassets()
  | [c;w] when c = "importprivkey" ->
      load_wallet();
      importprivkey w
  | [c;w] when c = "importbtcprivkey" ->
      load_wallet();
      importbtcprivkey w
  | [c;a;b;s] when c = "importendorsement" ->
      load_wallet();
      importendorsement a b s
  | [c;a] when c = "importwatchaddr" ->
      load_wallet();
      importwatchaddr a
  | [c;a] when c = "importwatchbtcaddr" ->
      load_wallet();
      importwatchbtcaddr a
  | [c;a] when c = "btctoqedaddr" ->
      btctoqedaddr a
  | (c::pl) when c = "frameallpos" ->
      localframe := load_currentframe();
      List.iter (fun p -> localframe := frame_set_all_pos !localframe (bitstr_bitseq p)) pl;
      save_currentframe !localframe
  | (c::pl) when c = "framehashpos" ->
      localframe := load_currentframe();
      List.iter (fun p -> localframe := frame_set_hash_pos !localframe (bitstr_bitseq p)) pl;
      save_currentframe !localframe
  | (c::pl) when c = "frameabbrevpos" ->
      localframe := load_currentframe();
      List.iter (fun p -> localframe := frame_set_abbrev_pos !localframe (bitstr_bitseq p)) pl;
      save_currentframe !localframe
  | (c::levels) when c = "frameabbrevlevel" ->
      localframe := load_currentframe();
      List.iter (fun l -> localframe := frame_set_abbrev_level !localframe (int_of_string l)) levels;
      save_currentframe !localframe
  | (c::addrs) when c = "frameaddrs" ->
      begin
	let l = List.length addrs in
	if l = 0 then
	  raise (Failure "frameaddrs was given no addresses")
	else
	  let ll = List.nth addrs (l-1) in
	  try
	    let i = int_of_string ll in
	    localframe := load_currentframe();
	    List.iter (fun alpha -> if not (alpha = ll) then localframe := frame_add_leaf !localframe (Cryptocurr.qedaddrstr_addr alpha) (Some(i))) addrs;
	    save_currentframe !localframe
	  with Failure("int_of_string") ->
	    localframe := load_currentframe();
	    List.iter (fun alpha -> localframe := frame_add_leaf !localframe (Cryptocurr.qedaddrstr_addr alpha) None) addrs;
	    save_currentframe !localframe
      end
(***
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
