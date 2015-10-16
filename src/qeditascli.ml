(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ctre;;
open Net;;
open Setconfig;;
open Commands;;

let commhelp = [
("importprivkey",1,Some 1,"importprivkey <Qeditas WIF>","Import the private key for a Qeditas p2pkh address into the local wallet.");
("importbtcprivkey",1,Some 1,"importbtcprivkey <Bitcoin WIF>","Import a private key (in Bitcoin WIF format) for a Qeditas p2pkh address into the local wallet.");
("importendorsement",3,Some 3,"importendorsement <address 1> <address 2> <Bitcoin message signature>","Import an endorsement of Qeditas pay address 1 to Qeditas pay address 2 (so that address 2 can sign for address 1).");
("importwatchaddr",1,Some 1,"importwatchaddr <address>","Import an address into the wallet in order to watch the address.");
("importbtcwatchaddr",1,Some 1,"importbtcwatchaddr <Bitcoin address>","Import a Qeditas pay address by giving the corresponding Bitcoin address.
The address is only watched, not controlled.");
("btctoqedaddr",1,Some 1,"btctoqedaddr <Bitcoin address>","Give the Qeditas pay address corresponding to the given Bitcoin address. The wallet is not affected.");
("printassets",0,Some 0,"printassets","Print the assets held at the addresses in the wallet.
This may include addresses that are only watched, not controlled.");
("frameallpos",1,None,"frameallpos [position ... position]","Give positions at which the local frame should keep up with all of the ledger tree beneath the position.
Positions are specified with strings consisting of 0s and 1s.");
("framehashpos",1,None,"framehashpos [position ... position]","Give positions at which the local frame should not keep up with the ledger tree beneath the position,
but should summarize the tree beneath the position with a hash root.
Positions are specified with strings consisting of 0s and 1s.");
("frameabbrevpos",1,None,"frameabbrevpos [position ... position]","Give positions at which the local frame should save the ledger tree in a file as an abbreviations.
Positions are specified with strings consisting of 0s and 1s.");
("frameabbrevlevel",1,None,"frameabbrevlevel [level ... level]","Give levels at which the local frame should save the ledger tree in a file as an abbreviations.
Levels are integers between 0 and 160.

Example:
frameabbrevlevel 8 16
indicates that all ctree nodes 8 levels deep and 16 levels deep should be
saved as abbreviations in files and represented in memory as an abbreviation
referring to the file.");
("frameaddrs",1,None,"frameaddrs [<address> ... <address>] [n]","Change the local frame (if necessary) to ensure that the leaves of the ledger tree corresponding
to the addresses are kept up with. If the last argument is an integer n, then only the first n
assets of those leaves are kept up with, with the remaining assets summarized by a hash root.");
("help",0,Some 1,"help [command]","Give a list of commands or help for a specific command.")
];;

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
  | [c] when c = "help" ->
      List.iter
	(fun (x,_,_,sh,_) -> Printf.printf "%s: %s\n" x sh)
	commhelp
  | [c;x] when c = "help" ->
      begin
	try
	  match List.find (fun (x1,_,_,_,_) -> x1 = x) commhelp with
	  | (_,_,_,sh,lh) ->
	      Printf.printf "%s\n%s\n" sh lh;
	with Not_found ->
	  Printf.printf "Unknown command %s.\n" x;
	  raise (Failure "Unknown command")
      end
  | (c::_) -> 
      begin
	try
	  match List.find (fun (x,_,_,_,_) -> x = c) commhelp with
	  | (_,a,_,sh,_) when List.length r < a+1 ->
	      Printf.printf "%s expects at least %d arguments.\n%s\n" c a sh;
	  | (_,_,Some(b),sh,_) when List.length r > b+1 ->
	      Printf.printf "%s expects at most %d arguments.\n%s\n" c b sh;
	  | _ ->
	      Printf.printf "Error handling %s\nIt's possible some code has not yet been written.\n" c;
	with Not_found ->
	  Printf.printf "Unknown command %s.\n" c;
	  raise (Failure "Unknown command")
      end
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
