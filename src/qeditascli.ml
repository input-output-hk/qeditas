(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser;;
open Hash;;
open Ctre;;
open Net;;
open Setconfig;;
open Commands;;

let random_int32_array : int32 array = [| 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l; 0l |];;
let random_initialized : bool ref = ref false;;

(*** generate 512 random bits and then use sha256 on them each time we need a new random number ***)
let initialize_random_seed () =
  let r = open_in_bin (if !Config.testnet then "/dev/urandom" else "/dev/random") in
  let v = ref 0l in
  for i = 0 to 15 do
    v := 0l;
    for j = 0 to 3 do
      v := Int32.logor (Int32.shift_left !v 8) (Int32.of_int (input_byte r))
    done;
    random_int32_array.(i) <- !v;
  done;
  random_initialized := true;;

let sha256_random_int32_array () =
  Sha256.sha256init();
  for i = 0 to 15 do
    Sha256.currblock.(i) <- random_int32_array.(i)
  done;
  Sha256.sha256round();
  let (x7,x6,x5,x4,x3,x2,x1,x0) = Sha256.getcurrmd256() in
  for i = 0 to 7 do
    random_int32_array.(i+8) <- random_int32_array.(i)
  done;
  random_int32_array.(0) <- x0;
  random_int32_array.(1) <- x1;
  random_int32_array.(2) <- x2;
  random_int32_array.(3) <- x3;
  random_int32_array.(4) <- x4;
  random_int32_array.(5) <- x5;
  random_int32_array.(6) <- x6;
  random_int32_array.(7) <- x7;;

let rand_256 () =
  if not !random_initialized then initialize_random_seed();
  sha256_random_int32_array();
  Sha256.md256_big_int (Sha256.getcurrmd256())

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
("createrawtransaction",2,None,"createrawtransaction <input> ... <input> out <output> ... <output>","Create a transaction with the specified inputs and outputs.
Each <input> is specified by giving <address>:<assetid>.
An <assetid> is a 40 character hex string indicating the hash associated with the asset.
Each output is specified by giving <address>:<preasset> or <address>:<obligation>:<preasset>.
An <obligation> (if given) is of the form <address>,<int>.
A <preasset> is one of the following forms:

<num> (interpreted as the specified number of fraenks as currency units)
bounty:<num> * (interpreted as the specified number of fraenks as a bounty on a conjecture)
ownsobj:<address>:<rightsinfo> *
ownsprop:<address>:<rightsinfo> *
ownsnegprop *
rightsobj:<address>:<int> *
rightsprop:<address>:<int> *
marker
theory:<address>:<theoryname> *
signa:<address>:<signaturename>[:<theoryname>] *
doc:<address>:<documentname>[:<theoryname>] *

* The options marked with * are not yet implemented.

Created transactions are appended to the 'recenttxs' file.");
("signrawtransaction",1,Some(1),"signrawtransaction <txid>","Sign a transaction (partially or completely) depending on what information is in the wallet.
The (partially) signed transaction is added to the 'recenttxs' file.");
("sendrawtransaction",1,Some(1),"sendrawtransaction <txid>","If the tx is completely signed, put it in the 'txpool' file. qeditasd will then publish it.");
("help",0,Some 1,"help [command]","Give a list of commands or help for a specific command.")
];;

datadir_from_command_line();; (*** if -datadir=... is on the command line, then set Config.datadir so we can find the config file ***)
process_config_file();;
process_config_args();; (*** settings on the command line shadow those in the config file ***)

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

let separate_by_char x c =
  let b = Buffer.create 30 in
  let rl = ref [] in
  for i = 0 to (String.length x) - 1 do
    let d = x.[i] in
    if d = c then
      begin
	rl := Buffer.contents b::!rl;
	Buffer.clear b
      end
    else
      Buffer.add_char b d
  done;
  let y = Buffer.contents b in
  if not (y = "") then rl := y::!rl;
  List.rev !rl

let parse_tx_input x =
  match separate_by_char x ':' with
  | [alphastr;aid] ->
      (Cryptocurr.qedaddrstr_addr alphastr,hexstring_hashval aid)
  | _ -> raise (Failure "An input should be of the form <address>:<assetid>")

let parse_obligation x =
  match separate_by_char x ',' with
  | [betastr;y] ->
      let beta = Cryptocurr.qedaddrstr_addr betastr in
      let h = Int64.of_string y in
      let (i,x4,x3,x2,x1,x0) = beta in
      if i = 0 then
	((false,x4,x3,x2,x1,x0),h,false)
      else if i = 0 then
	((true,x4,x3,x2,x1,x0),h,false)
      else
	raise (Failure "only pay addresses can be used in obligations")
  | _ -> raise (Failure "incorrect format for obligation")

let parse_fraenks x =
  match separate_by_char x '.' with
  | [w] -> Int64.mul (Int64.of_string w) 1000000000000L
  | [w;d] ->
      let dl = String.length d in
      if dl > 12 then
	raise (Failure "not a specification of an amount of fraenks")
      else
	let b = Buffer.create 12 in
	for i = dl to 11 do
	  Buffer.add_char b '0'
	done;
	Int64.add (Int64.mul (Int64.of_string w) 1000000000000L) (Int64.of_string (String.concat "" [d;Buffer.contents b]))
  | _ -> raise (Failure "not a specification of an amount of fraenks")

let parse_preasset xl =
  match xl with
  | [mrk] when mrk = "marker" -> Assets.Marker
  | [fraenks] ->
      let v = parse_fraenks fraenks in
      Assets.Currency(v)
  | _ -> raise (Failure "either not a preasset or unwritten case")

let parse_tx_output x =
  match separate_by_char x ':' with
  | [] -> raise (Failure "An output should be of the form <address>[:<obligation>]:<preasset>")
  | (alphastr::rst) ->
      let alpha = Cryptocurr.qedaddrstr_addr alphastr in
      match rst with
      | [] -> raise (Failure "An output should be of the form <address>[:<obligation>]:<preasset>")
      | (oblstr::rst2) ->
	  try
	    let obl = parse_obligation oblstr in
	    let u = parse_preasset rst2 in
	    (alpha,Some(obl),u)
	  with Failure(_) ->
	    let u = parse_preasset rst in
	    (alpha,None,u)

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
  | (c::args) when c = "createrawtransaction" ->
      let argl = ref args in
      let inarg = ref true in
      let inl = ref [] in
      let outl = ref [] in
      begin
	while not (!argl = []) do
	  match !argl with
	  | [] -> () (*** impossible ***)
	  | (x::argr) when x = "out" && !inarg -> inarg := false; argl := argr
	  | (x::argr) ->
	      argl := argr;
	      if !inarg then
		let (alpha,aid) = parse_tx_input x in
		inl := (alpha,aid)::!inl
	      else
		let (alpha,obl,u) = parse_tx_output x in
		outl := (alpha,(obl,u))::!outl
	done;
	let tau = (List.rev !inl,List.rev !outl) in
	if not (Tx.tx_valid tau) then raise (Failure "invalid tx");
	let txid = Tx.hashtx tau in
	Printf.printf "Txid: %s\n" (hashval_hexstring txid); flush stdout;
	let fn = Filename.concat !Config.datadir "recenttxs" in
	if Sys.file_exists fn then
	  begin
	    let ch = open_out_gen [Open_wronly;Open_binary;Open_append] 0o644 fn in
	    seocf (seo_prod seo_hashval Tx.seo_stx seoc (txid,(tau,([],[]))) (ch,None));
	    close_out ch
	  end
	else
	  begin
	    let ch = open_out_gen [Open_wronly;Open_binary;Open_creat] 0o644 fn in
	    seocf (seo_prod seo_hashval Tx.seo_stx seoc (txid,(tau,([],[]))) (ch,None));
	    close_out ch
	  end
      end
  | [c;txid] when c = "signrawtransaction" ->
      let txid = hexstring_hashval txid in
      begin
	load_recenttxs();
	try
	  let ((txin,txout),(sin,sout)) = Hashtbl.find recenttxs txid in
	  let sin2 = ref sin in
	  let sout2 = ref sout in
	  load_wallet();
	  List.iter
	    (fun (alpha,_) -> (*** for now, assume there's no obligation here (wrong in general, but need to look up the asset in the general case ***)
	      Printf.printf "alpha %s\n" (Cryptocurr.addr_qedaddrstr alpha);
	      let (i,x4,x3,x2,x1,x0) = alpha in
	      if i = 0 then (*** only handle p2pkh for now ***)
		try
		  let (k,b,(x,y),w,h,beta) = List.find (fun (k,b,(x,y),w,h,beta) -> h = (x4,x3,x2,x1,x0)) !walletkeys in
		  let ra = rand_256() in
		  Printf.printf "adding sig\n";
		  sin2 := (Script.P2pkhSignat(Some(x,y),b,Signat.signat_hashval txid k ra))::!sin2
		with Not_found ->
		  try
		    let (_,((j,y4,y3,y2,y1,y0) as beta),(w,z),recid,fcomp,esg) =
		      List.find (fun (alpha2,beta,(w,z),recid,fcomp,esg) -> payaddr_addr alpha2 = alpha) !walletendorsements
		    in
		    if not j then
		      let (k,b,(x,y),wif,h,gamma) = List.find (fun (k,b,(x,y),wif,h,beta) -> h = (y4,y3,y2,y1,y0)) !walletkeys in
		      let ra = rand_256() in
		      Printf.printf "adding sig by endorsement\n";
		      sin2 := (Script.EndP2pkhToP2pkhSignat(Some(w,z),fcomp,Some(x,y),b,esg,Signat.signat_hashval txid k ra))::!sin2
		    else
		      raise Not_found
		  with Not_found -> ()
	    )
	    txin;
	  (*** don't worry about sout for now; it's needed for publications ***)
	  if not (!sin2 = sin && !sout2 = sout) then
	    let fn = Filename.concat !Config.datadir "recenttxs" in
	    let ch = open_out_gen [Open_wronly;Open_binary;Open_append] 0o644 fn in
	    seocf (seo_prod seo_hashval Tx.seo_stx seoc (txid,((txin,txout),(!sin2,!sout2))) (ch,None));
	    close_out ch
	with Not_found ->
	  raise (Failure "Unknown tx")
      end
  | [c;txid] when c = "sendrawtransaction" ->
      let txid = hexstring_hashval txid in
      begin
	load_recenttxs();
	try
	  let stau = Hashtbl.find recenttxs txid in
	  let fn = Filename.concat !Config.datadir "txpool" in
	  if Sys.file_exists fn then
	    begin
	      let ch = open_out_gen [Open_wronly;Open_binary;Open_append] 0o644 fn in
	      seocf (seo_prod seo_hashval Tx.seo_stx seoc (txid,stau) (ch,None));
	      close_out ch
	    end
	  else
	    begin
	      let ch = open_out_gen [Open_wronly;Open_binary;Open_creat] 0o644 fn in
	      seocf (seo_prod seo_hashval Tx.seo_stx seoc (txid,stau) (ch,None));
	      close_out ch
	    end
	with Not_found ->
	  raise (Failure "Unknown tx")
      end
  | [c] when c = "printassets" ->
      localframe := load_currentframe();
      localframehash := hashframe !localframe;
      load_root_abbrevs_index();
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
