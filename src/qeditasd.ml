(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser;;
open Hash;;
open Assets;;
open Tx;;
open Ctre;;
open Block;;
open Net;;
open Setconfig;;

(*** recent (provisional) data ***)
(*** recentledgerroots: associate ledger (ctree) roots with a block height and abbrev hashval ***)
(*** recentblockheaders: associate block header hash with block height and block header ***)
(*** recentblockdeltahs: associate block header hash with a blockdeltah (summarizing stxs by hashvals) ***)
(*** recentblockdeltas: associate block header hash with a blockdelta (with all stxs explicit) ***)
(*** recentstxs: associate hashes of txs/stxs with stxs (may or may not be in blocks) ***)
let recentledgerroots : (hashval, int64 * hashval) Hashtbl.t = Hashtbl.create 1024;;
let recentblockheaders : (hashval, int64 * blockheader) Hashtbl.t = Hashtbl.create 1024;;
let recentblockdeltahs : (hashval, blockdeltah) Hashtbl.t = Hashtbl.create 1024;;
let recentblockdeltas : (hashval, blockdelta) Hashtbl.t = Hashtbl.create 1024;;
let recentstxs : (hashval, stx) Hashtbl.t = Hashtbl.create 65536;;

let stakingproccomm : (in_channel * out_channel * in_channel) option ref = ref None;;

let fallbacknodes = [
"108.61.219.125:20805"
];;

let testnetfallbacknodes = [
"108.61.219.125:20804"
];;

let conns = ref [];;

let rand_int64 () =
  let r = open_in_bin "/dev/random" in
  let get_byte r = Int64.of_int (input_byte r) in
  let v = Int64.shift_right_logical (get_byte r) 56 in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 48) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 40) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 32) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 24) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 16) in
  let v = Int64.logor v (Int64.shift_right_logical (get_byte r) 8) in
  let v = Int64.logor v (get_byte r) in
  close_in r;
  v;;

let myaddr () =
  match !Config.ip with
  | Some(ip) -> 
      if !Config.ipv6 then
	"[" ^ ip ^ "]:" ^ (string_of_int !Config.port)
      else
	ip ^ ":" ^ (string_of_int !Config.port)
  | None ->
      "";;

let initialize_conn_accept s =
  if List.length !conns < !Config.maxconns then
    begin
      let sin = Unix.in_channel_of_descr s in
      let sout = Unix.out_channel_of_descr s in
      set_binary_mode_in sin true;
      set_binary_mode_out sout true;
      try
	let m2 = rec_msg_nohang sin 5.0 5.0 in
	match m2 with
	| Some(_,_,Version(vers2,srvs2,tm2,addr_recv2,addr_from2,n2,user_agent2,fr20,fr21,fr22,first_header_height2,first_full_height2,last_height2,relay2,lastchkpt2)) ->
	    send_msg sout Verack;
	    let vers = 1l in
	    let srvs = 1L in
	    let tm = Int64.of_float(Unix.time()) in
	    let nonce = rand_int64() in
	    let user_agent = "Qeditas-Testing-Phase" in
	    let fr0 = RFAll in
	    let fr1 = RFAll in
	    let fr2 = RFAll in
	    let first_header_height = 0L in
	    let first_full_height = 0L in
	    let last_height = 0L in
	    let relay = true in
	    let lastchkpt = None in
	    send_msg sout (Version(vers,srvs,tm,addr_from2,myaddr(),nonce,user_agent,fr0,fr1,fr2,first_header_height,first_full_height,last_height,relay,lastchkpt));
	    let m1 = rec_msg_nohang sin 5.0 5.0 in
	    begin
	      match m1 with
	      | Some(_,_,Verack) ->
		  Printf.printf "Added connection; post handshake\nmy time = %Ld\ntheir time = %Ld\naddr_recv2 = %s\naddr_from2 = %s\n" tm tm2 addr_recv2 addr_from2; flush stdout;
		  let cs =
		    { alive = true;
		      lastmsgtm = Unix.time();
		      pending = [];
		      rframe0 = fr20;
		      rframe1 = fr21;
		      rframe2 = fr22;
		      first_header_height = first_header_height2;
		      first_full_height = first_full_height2;
		      last_height = last_height2;
		    }
		  in
		  conns := (s,sin,sout,addr_from2,cs)::!conns;
		  true
	      | _ ->
		  Printf.printf "Handshake failed. (No Verack)\n"; flush stdout;
		  Unix.close s;
		  false
	    end
	| _ ->
	    Printf.printf "Handshake failed. (No Version)\n"; flush stdout;
	    Unix.close s; (*** handshake failed ***)
	    false
      with
      | IllformedMsg ->
	  Printf.printf "Handshake failed. (IllformedMsg)\n"; flush stdout;
	  Unix.close s; (*** handshake failed ***)
	  false
    end
  else
    begin
      Printf.printf "Rejecting connection because of maxconns.\n"; flush stdout;
      Unix.close s;
      false
    end;;

let initialize_conn_2 n s sin sout =
  (*** handshake ***)
  let vers = 1l in
  let srvs = 1L in
  let tm = Int64.of_float(Unix.time()) in
  let nonce = rand_int64() in
  let user_agent = "Qeditas-Testing-Phase" in
  let fr0 = RFAll in
  let fr1 = RFAll in
  let fr2 = RFAll in
  let first_header_height = 0L in
  let first_full_height = 0L in
  let last_height = 0L in
  let relay = true in
  let lastchkpt = None in
  send_msg sout (Version(vers,srvs,tm,myaddr(),n,nonce,user_agent,fr0,fr1,fr2,first_header_height,first_full_height,last_height,relay,lastchkpt));
  try
    let m1 = rec_msg_nohang sin 5.0 5.0 in
    match m1 with
    | Some(_,_,Verack) ->
	begin
	  let m2 = rec_msg_nohang sin 5.0 5.0 in
	  match m2 with
	  | Some(_,_,Version(vers2,srvs2,tm2,addr_recv2,addr_from2,n2,user_agent2,fr20,fr21,fr22,first_header_height2,first_full_height2,last_height2,relay2,lastchkpt2)) ->
	      send_msg sout Verack;
	      Printf.printf "Added connection; post handshake\nmy time = %Ld\ntheir time = %Ld\naddr_recv2 = %s\naddr_from2 = %s\n" tm tm2 addr_recv2 addr_from2; flush stdout;
	      let cs =
		{ alive = true;
		  lastmsgtm = Unix.time();
		  pending = [];
		  rframe0 = fr20;
		  rframe1 = fr21;
		  rframe2 = fr22;
		  first_header_height = first_header_height2;
		  first_full_height = first_full_height2;
		  last_height = last_height2;
		}
	      in
	      conns := (s,sin,sout,addr_from2,cs)::!conns;
	      true
	  | _ ->
	      Printf.printf "Handshake failed. (No Version)\n"; flush stdout;
	      Unix.close s; (*** handshake failed ***)
	      false
	end
    | _ ->
	begin (*** handshake failed ***)
	  Printf.printf "Handshake failed. (No Verack)\n"; flush stdout;
	  Unix.close s;
	  false
	end
  with
  | IllformedMsg ->
      Printf.printf "Handshake failed. (IllformedMsg)\n"; flush stdout;
      Unix.close s; (*** handshake failed ***)
      false;;

let initialize_conn n s =
  let sin = Unix.in_channel_of_descr s in
  let sout = Unix.out_channel_of_descr s in
  set_binary_mode_in sin true;
  set_binary_mode_out sout true;
  initialize_conn_2 n s sin sout;;

exception Connected;;

let search_for_conns () =
  if !conns = [] then
    begin
      try
	List.iter
	  (fun n ->
	    let (ip,port,v6) = extract_ip_and_port n in
	    if not (!Config.ip = Some(ip) && !Config.ipv6 = v6) then (*** if this is a fallback node, do not connect to itself ***)
	      begin
		try
		  match !Config.socks with
		  | None ->
		      let s = connectpeer ip port in
		      ignore (initialize_conn n s)
		  | Some(4) ->
		      let (s,sin,sout) = connectpeer_socks4 !Config.socksport ip port in
		      ignore (initialize_conn_2 n s sin sout)
		  | Some(5) ->
		      raise (Failure "socks5 is not yet supported")
		  | Some(z) ->
		      raise (Failure ("socks" ^ (string_of_int z) ^ " is not yet supported"))
		with
		| RequestRejected -> Printf.printf "RequestRejected\n"; flush stdout;
		| Connected -> raise Connected
		| _ -> ()
	      end
	  )
	(if !Config.testnet then testnetfallbacknodes else fallbacknodes)
      with Connected -> ()
    end;;

let rec hlist_insertstakingassets tostkr alpha hl =
  match hl with
  | HCons((aid,bday,obl,Currency(v)),hr) ->
      Commands.stakingassets := (alpha,aid,bday,obl,v)::!Commands.stakingassets;
      output_byte tostkr 67;
      seocf (seo_hashval seoc alpha (tostkr,None));
      seocf (seo_hashval seoc aid (tostkr,None));
      seocf (seo_int64 seoc bday (tostkr,None));
      seocf (seo_int64 seoc v (tostkr,None));
      seocf (seo_obligation seoc obl (tostkr,None));
      hlist_insertstakingassets tostkr alpha hr
  | HCons(_,hr) -> hlist_insertstakingassets tostkr alpha hr
  | _ -> ();;

let main () =
  begin
    process_config_args();
    process_config_file();
    if !Config.seed = "" && !Config.lastcheckpoint = "" then
      begin
	raise (Failure "Need either a seed (to validate the genesis block) or a lastcheckpoint (to start later in the blockchain); have neither")
      end;
    if not (!Config.seed = "") then
      begin
	if not (String.length !Config.seed = 40) then raise (Failure "Bad seed");
	try
	  set_genesis_stakemods !Config.seed
	with
	| Invalid_argument(_) ->
	    raise (Failure "Bad seed")
      end;
    let l = 
      match !Config.ip with
      | Some(ip) ->
	  let l = openlistener ip !Config.port 5 in
	  Printf.printf "Listening for incoming connections.\n";
	  flush stdout;
	  Some(l)
      | None ->
	  Printf.printf "Not listening for incoming connections.\nIf you want Qeditas to listen for incoming connections set ip to your ip address\nusing ip=... in qeditas.conf or -ip=... on the command line.\n";
	  flush stdout;
	  None
    in
    if !Config.staking then (*** start a staking process ***)
      begin
	let stkexec = Filename.concat (Filename.dirname (Sys.argv.(0))) "qeditasstk" in
	Printf.printf "about to start staker\n"; flush stdout;
	let (fromstkr,tostkr,stkerr) = Unix.open_process_full stkexec [||] in
	Printf.printf "started staker\n"; flush stdout;
	let reasontostake = ref false in
	stakingproccomm := Some(fromstkr,tostkr,stkerr);
	Commands.read_wallet();
	List.iter
	  (fun (k,b,(x,y),w,h,alpha) ->
	    let ctr = Ctre.CAbbrev(hexstring_hashval "7b47514ebb7fb6ab06389940224d09df2951e97e",hexstring_hashval "df418292e7c54837ebdd3962cbfee9d4bc8ca981") in
	    match Ctre.ctree_addr (hashval_p2pkh_addr h) ctr with
	    | (Some(Ctre.CLeaf(_,hl)),_) ->
		reasontostake := true;
		hlist_insertstakingassets tostkr h (Ctre.nehlist_hlist hl)
	    | _ ->
		()
	  )
	  !Commands.walletkeys;
	flush tostkr;
	let blkh = 0L in
	let tar = !genesistarget in
	let csm = !genesiscurrentstakemod in
	output_byte tostkr 66; (*** send the staking process the block height, the target and the stake modifier ***)
	seocf (seo_int64 seoc blkh (tostkr,None));
	seocf (seo_big_int_256 seoc tar (tostkr,None));
	seocf (seo_stakemod seoc csm (tostkr,None));
	output_byte tostkr 83; (*** start staking ***)
	flush tostkr
      end;
    sethungsignalhandler();
    search_for_conns ();
    while true do (*** main process loop ***)
      try
	begin (*** if staking check to see if staking has found a hit ***)
	  match !stakingproccomm with
	  | None -> ()
	  | Some(fromstkr,tostkr,stkerr) ->
	      try
		match input_byte_nohang fromstkr 0.1 with
		| Some(z) when z = 72 -> (*** hit with no storage ***)
		    let c = (fromstkr,None) in
		    let (stktm,c) = sei_int64 seic c in
		    let (alpha,c) = sei_hashval seic c in
		    let (aid,_) = sei_hashval seic c in
		    Printf.printf "Asset %s at address %s can stake at time %Ld (%Ld seconds from now)\n" (hashval_hexstring aid) (Cryptocurr.addr_qedaddrstr (hashval_p2pkh_addr alpha)) stktm (Int64.sub stktm (Int64.of_float (Unix.time())));
		    flush stdout;
		    begin
		      try
			let (_,_,bday,obl,v) = List.find (fun (_,h,_,_,_) -> h = aid) !Commands.stakingassets in
			if check_hit_b 0L bday obl v !genesiscurrentstakemod !genesistarget stktm aid alpha None then
			  Printf.printf "Confirmed\n"
			else
			  Printf.printf "Bug. Not really a hit.\n"
		      with Not_found -> Printf.printf "Bug. Cannot find staking asset.\n"
		    end;
		    flush stdout;
		| Some(z) when z = 83 -> (*** hit with storage ***)
		    ()
		| Some(z) -> (*** something has gone wrong. die ***)
		    Printf.printf "The staking process sent back %d which is meaningless.\nKilling staker\n" z;
		    Unix.close_process_full (fromstkr,tostkr,stkerr);
		    stakingproccomm := None
		| None ->
		    match input_byte_nohang stkerr 0.1 with
		    | Some(z) -> (*** something has gone wrong. die ***)
			Printf.printf "The staking process sent error code %d.\nKilling staker\n" z;
			Unix.close_process_full (fromstkr,tostkr,stkerr);
			stakingproccomm := None
		    | None -> ()
	      with
	      | _ ->
		  Printf.printf "Exception thrown while trying to read from the staking process.\nKilling staker\n";
		  Unix.close_process_full (fromstkr,tostkr,stkerr);
		  stakingproccomm := None
	end;
	begin (*** possibly check for a new incomming connection ***)
	  match l with
	  | Some(l) ->
	      begin
		match accept_nohang l 0.1 with
		| Some(s,a) ->
		    begin
		      match a with
		      | Unix.ADDR_UNIX(x) ->
			Printf.printf "got local connection %s\n" x;
		      | Unix.ADDR_INET(x,y) ->
			  Printf.printf "got remote connection %s %d\n" (Unix.string_of_inet_addr x) y;
		    end;
		    flush stdout;
		    if initialize_conn_accept s then
		      Printf.printf "accepted remote connection\n"
		    else
		      Printf.printf "rejected remote connection\n";
		    flush stdout;
		| None -> ()
	      end
	  | None -> ()
	end;
	(*** check each connection for possible messages ***)
	List.iter
	  (fun (s,sin,sout,peeraddr,cs) ->
	    try
	      let tm = Unix.time() in
	      match rec_msg_nohang sin 0.1 1.0 with
	      | None ->
		  begin
		    try
		      ignore (List.find (fun (h,p,tm1,tm2,f) -> p && (tm -. tm2 > 30.0)) cs.pending);
			(*** Something that required a response didn't respond in time (e.g., a Ping).
			     Drop the connection
			 ***)
                      Printf.printf "Ping-Pong failed. Dropping connection.\n"; flush stdout;
                      Unix.close s;
                      cs.alive <- false
                    with Not_found ->
		    if (tm -. cs.lastmsgtm) > 60.0 then (*** If no messages in enough time, send a ping. ***)
		      begin
			Printf.printf "Sending Ping.\n"; flush stdout;
			let mh = send_msg sout Ping in
			Printf.printf "Sent Ping.\n"; flush stdout;
                        cs.pending <- (mh,true,tm,tm,None)::cs.pending;
                        cs.lastmsgtm <- tm
		      end
		  end
	      | Some(replyto,mh,m) ->
		begin
		  Printf.printf "got a msg, new lastmsgtm %f\n" tm; flush stdout;
                  cs.lastmsgtm <- tm;
		  handle_msg sin sout cs replyto mh m
		end
	    with
	    | End_of_file ->
		Printf.printf "Lost connection.\n"; flush stdout;
		cs.alive <- false
	    | IllformedMsg ->
		Printf.printf "IllformedMsg. Breaking connection.\n"; flush stdout;
		cs.alive <- false
	    | exn -> (*** unexpected ***)
		Printf.printf "Other exception: %s\nNot dropping connection yet.\n" (Printexc.to_string exn);
	  )
	  !conns;
	conns := List.filter (fun (s,sin,sout,peeraddr,cs) -> cs.alive) !conns
      with _ -> () (*** ensuring no exception escapes the main loop ***)
    done
  end;;

let stop_staking () =
  match !stakingproccomm with
  | Some(sti,sto,ste) -> ignore (Unix.close_process_full (sti,sto,ste))
  | None -> ();;

try
  main ()
with
| Failure(x) ->
    Printf.printf "%s\nExiting.\n" x;
    stop_staking ()
| exn -> (*** unexpected ***)
    Printf.printf "Exception: %s\nExiting.\n" (Printexc.to_string exn);
    stop_staking ();;
