(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int;;
open Utils;;
open Ser;;
open Hash;;
open Net;;
open Db;;
open Secp256k1;;
open Signat;;
open Assets;;
open Tx;;
open Ctre;;
open Ctregraft;;
open Block;;
open Blocktree;;
open Setconfig;;

let stkth : Thread.t option ref = ref None;;

let initnetwork () =
  begin
    try
      match !Config.ip with
      | Some(ip) ->
	  let l = openlistener ip !Config.port 5 in
	  Printf.printf "Listening for incoming connections.\n";
	  flush stdout;
	  netlistenerth := Some(Thread.create netlistener l)
      | None ->
	  Printf.printf "Not listening for incoming connections.\nIf you want Qeditas to listen for incoming connections set ip to your ip address\nusing ip=... in qeditas.conf or -ip=... on the command line.\n";
	  flush stdout
    with _ -> ()
  end;
  netseeker ();
  (*** empty placeholder for now ***)
  ();;

type nextstakeinfo = NextStake of (int64 * int64 * hashval * blockheader * blockdelta * big_int * blocktree) | NoStakeUpTo of int64;;

let nextstakechances : (hashval option,nextstakeinfo) Hashtbl.t = Hashtbl.create 100;;

let rec hlist_stakingassets alpha hl =
  match hl with
  | HCons((aid,bday,obl,Currency(v)),hr) ->
(*** lock stakingassets ***)
      Commands.stakingassets := (alpha,aid,bday,obl,v)::!Commands.stakingassets;
(*** unlock stakingassets ***)
      hlist_stakingassets alpha hr
  | HCons(_,hr) -> hlist_stakingassets alpha hr
  | _ -> ();;

let compute_staking_chances n fromtm totm =
   let i = ref fromtm in
   let BlocktreeNode(par,children,prevblk,thyroot,sigroot,currledgerroot,prevtinfo,currtinfo,deltm,tmstamp,prevcumulstk,blkhght,validated,blacklisted,succl) = n in
   let (csm1,fsm1,tar1) = currtinfo in
   let c = CHash(currledgerroot) in
   (*** collect assets allowed to stake now ***)
   Commands.stakingassets := [];
   List.iter
     (fun (k,b,(x,y),w,h,alpha) ->
      Printf.fprintf !log "about to get assets from %s for staking\n" alpha; flush !log;
      if not (is_recent_staker h n 6) then
         match ctree_addr (hashval_p2pkh_addr h) c None with
         | (Some(hl),_) ->
            hlist_stakingassets h (nehlist_hlist hl)
         | _ -> ())
    !Commands.walletkeys;
  List.iter
    (fun (alpha,beta,_,_,_,_) ->
      Printf.printf "about to get assets from %s for staking via endorsement\n" (Cryptocurr.addr_qedaddrstr (payaddr_addr alpha)); flush stdout;
      let (p,x4,x3,x2,x1,x0) = alpha in
      let (q,_,_,_,_,_) = beta in
      if not p && not q then (*** only p2pkh can stake ***)
	if not (is_recent_staker (x4,x3,x2,x1,x0) n 6) then
	  match ctree_addr (payaddr_addr alpha) c None with
	  | (Some(hl),_) ->
	      hlist_stakingassets (x4,x3,x2,x1,x0) (nehlist_hlist hl)
	  | _ -> ())
    !Commands.walletendorsements;
  try
    while !i < totm do
      i := Int64.add 1L !i;
      (*** go through assets and check for staking at time !i ***)
      List.iter
	(fun (stkaddr,h,bday,obl,v) ->
	    let mtar = mult_big_int tar1 (coinage blkhght bday obl (incrstake v)) in
	    let ntar = mult_big_int tar1 (coinage blkhght bday obl v) in
	    output_string !log ("i := " ^ (Int64.to_string !i) ^ "\nh := " ^ (Hash.hashval_hexstring h) ^ "\n");
	    let (m3,m2,m1,m0) = csm1 in
	    output_string !log ("csm1 := (" ^ (Int64.to_string m3) ^ "," ^ (Int64.to_string m2) ^ "," ^ (Int64.to_string m1) ^ "," ^ (Int64.to_string m0) ^ ")\n");
	    output_string !log ("ntar   := " ^ (string_of_big_int ntar) ^ "\n");
	    output_string !log ("hitval := " ^ (string_of_big_int (hitval !i h csm1)) ^ "\n");
	    flush !log;
	    (*** first check if it would be a hit with some storage component: ***)
	    if lt_big_int (hitval !i h csm1) mtar then
	      begin (*** if so, then check if it's a hit without some storage component ***)
		if lt_big_int (hitval !i h csm1) ntar then
		  begin
                    output_string !log "staked\n"; flush !log;
                    let fake_blockdelta = { stakeoutput = []; forfeiture = None; prevledgergraft = []; blockdelta_stxl = [] } in
                    let fake_blocktree = BlocktreeNode(None,ref [],None,None,None,h,currtinfo,currtinfo,1l,1L,zero_big_int,0L,ref Invalid,ref false,ref []) in
		    Hashtbl.add nextstakechances prevblk (NextStake(!i,0L,h,fake_blockheader,fake_blockdelta,zero_big_int,fake_blocktree)); (** mostly fake for now until the relevant code is updated ***)
		    raise Exit
		  end
		else (*** if not, check if there is some storage that will make it a hit [todo] ***)
		  begin
                    ()
(***
		    try
		      let (th,m,a,h,betak) =
			List.find
			  (fun (th,m,a,h,betak) ->
			    lt_big_int (hitval !i betak csm1) mtar)
			  !corrstrtrmassets
		      in
(***
		      staking := false;
		      output_byte stdout 83; (*** Report Hit With Storage ***)
		      let c = (stdout,None) in
		      let c = seo_int64 seoc !i c in
		      let c = seo_hashval seoc stkaddr c in
		      let c = seo_hashval seoc h c in
		      let c = seo_postor seoc (PostorTrm(th,m,a,h)) c in
		      seocf c;
***)
		      raise Exit
		    with Not_found ->
		      try
			let (gamma,nonce,th,d,h,betak) =
			  List.find
			    (fun (gamma,nonce,th,d,h,betak) ->
			      lt_big_int (hitval !i betak csm1) mtar)
			    !corrstrdocassets
			in
(***
			staking := false;
			output_byte stdout 83; (*** Report Hit With Storage ***)
			let c = (stdout,None) in
			let c = seo_int64 seoc !i c in
			let c = seo_hashval seoc stkaddr c in
			let c = seo_hashval seoc h c in
			let c = seo_postor seoc (PostorDoc(gamma,nonce,th,d,h)) c in
			seocf c;
			flush stdout;
***)
                        raise Exit
		      with Not_found -> () (*** not a hit at all ***)
***)
		  end
	      end)
	!Commands.stakingassets
    done;
    Hashtbl.add nextstakechances prevblk (NoStakeUpTo(totm));
  with Exit -> ();;

let stakingthread () =
  while true do
    try
      Unix.sleep 60;
      let best = !bestnode in
      try
        match Hashtbl.find nextstakechances (node_prevblockhash best) with
	| NextStake(_) -> ()
	| NoStakeUpTo(tm) ->
	    let ftm = Int64.add (Int64.of_float (Unix.time())) 3600L in
	    if tm < ftm then
	      compute_staking_chances best tm ftm
      with Not_found ->
	compute_staking_chances best (node_timestamp best) (Int64.add (Int64.of_float (Unix.time())) 7200L)
    with _ -> ()
  done;;

let sincetime f =
  let snc = Int64.of_float (Unix.time() -. f) in
  if snc >= 172800L then
    (Int64.to_string (Int64.div snc 86400L)) ^ " days"
  else if snc >= 7200L then
    (Int64.to_string (Int64.div snc 7200L)) ^ " hours"
  else if snc >= 120L then
    (Int64.to_string (Int64.div snc 60L)) ^ " minutes"
  else if snc = 1L then
    "1 second"
  else
    (Int64.to_string snc) ^ " seconds";;

let rec parse_command_r l i n =
  if i < n then
    let j = ref i in
    while !j < n && l.[!j] = ' ' do
      incr j
    done;
    let b = Buffer.create 20 in
    while !j < n && not (List.mem l.[!j] [' ';'"']) do
      Buffer.add_char b l.[!j];
      incr j
    done;
    let a = Buffer.contents b in
    let c d = if a = "" then d else a::d in
    if !j < n && l.[!j] = '"' then
      c (parse_command_r_q l (!j+1) n)
    else
      c (parse_command_r l (!j+1) n)
  else
    []
and parse_command_r_q l i n =
  let b = Buffer.create 20 in
  let j = ref i in
  while !j < n && not (l.[!j] = '"') do
    Buffer.add_char b l.[!j];
    incr j
  done;
  if !j < n then
    Buffer.contents b::parse_command_r l (!j+1) n
  else
    raise (Failure("missing quote"))

let parse_command l =
  let ll = parse_command_r l 0 (String.length l) in
  match ll with
  | [] -> raise Exit (*** empty command, silently ignore ***)
  | (c::al) -> (c,al)

let do_command l =
  let (c,al) = parse_command l in
  match c with
  | "exit" ->
      (*** Could call Thread.kill on netth and stkth, but Thread.kill is not always implemented. ***)
      closelog();
      exit 0
  | "getpeerinfo" ->
      remove_dead_conns();
      let ll = List.length !netconns in
      Printf.printf "%d connection%s\n" ll (if ll = 1 then "" else "s");
      List.iter
	(fun (_,(_,_,_,gcs)) ->
	  match !gcs with
	  | Some(cs) ->
	      Printf.printf "%s (%s): %s\n" cs.realaddr cs.addrfrom cs.useragent;
	      let snc = Int64.of_float (Unix.time() -. cs.conntime) in
	      let snc1 = sincetime cs.conntime in
	      let snc2 = sincetime cs.lastmsgtm in
	      Printf.printf "Connected for %s; last message %s ago.\n" snc1 snc2;
	      if cs.handshakestep < 5 then Printf.printf "(Still in handshake phase)\n";
	  | None -> (*** This could happen if a connection died after remove_dead_conns above. ***)
	      Printf.printf "[Dead Connection]\n";
	  )
	!netconns;
      flush stdout
  | "nettime" ->
      let (tm,skew) = network_time() in
      Printf.printf "network time %Ld (median skew of %d)\n" tm skew;
      flush stdout;
  | "printassets" when al = [] -> Commands.printassets()
  | "printassets" -> List.iter (fun h -> Commands.printassets_in_ledger (hexstring_hashval h)) al
  | "importprivkey" -> List.iter Commands.importprivkey al
  | "importbtcprivkey" -> List.iter Commands.importbtcprivkey al
  | "importwatchaddr" -> List.iter Commands.importwatchaddr al
  | "importwatchbtcaddr" -> List.iter Commands.importwatchbtcaddr al
  | "importendorsement" ->
      begin
	match al with
	| [a;b;s] -> Commands.importendorsement a b s
	| _ -> raise (Failure "importendorsement should be given three arguments: a b s where s is a signature made with the private key for address a endorsing to address b")
      end
  | "btctoqedaddr" -> List.iter Commands.btctoqedaddr al
  | "printasset" ->
      begin
	match al with
	| [h] -> Commands.printasset (hexstring_hashval h)
	| _ -> raise (Failure "printasset <assetid>")
      end
  | "printhconselt" ->
      begin
	match al with
	| [h] -> Commands.printhconselt (hexstring_hashval h)
	| _ -> raise (Failure "printhconselt <hashval>")
      end
  | "printctreeelt" ->
      begin
	match al with
	| [h] -> Commands.printctreeelt (hexstring_hashval h)
	| _ -> raise (Failure "printctreeelt <hashval>")
      end
  | "printctreeinfo" ->
      begin
	match al with
	| [] ->
	    let best = !bestnode in
	    let BlocktreeNode(_,_,_,_,_,currledgerroot,_,_,_,_,_,_,_,_,_) = best in
	    Commands.printctreeinfo currledgerroot
	| [h] -> Commands.printctreeinfo (hexstring_hashval h)
	| _ -> raise (Failure "printctreeinfo [ledgerroot]")
      end
  | _ ->
      (Printf.fprintf stdout "Ignoring unknown command: %s\n" c; List.iter (fun a -> Printf.printf "%s\n" a) al; flush stdout);;

let initialize () =
  begin
    datadir_from_command_line(); (*** if -datadir=... is on the command line, then set Config.datadir so we can find the config file ***)
    process_config_file();
    process_config_args(); (*** settings on the command line shadow those in the config file ***)
    if not !Config.testnet then (Printf.printf "Qeditas can only be run on testnet for now. Please give the -testnet command line argument.\n"; exit 0);
    let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
    let dbdir = Filename.concat datadir "db" in
    dbconfig dbdir; (*** configure the database ***)
    openlog(); (*** Don't open the log until the config vars are set, so if we know whether or not it's testnet. ***)
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
    if !Config.testnet then
      begin
	max_target := shift_left_big_int unit_big_int 230; (*** make the max_target higher (so difficulty can be easier for testing) ***)
	genesistarget := shift_left_big_int unit_big_int 200; (*** make the genesistarget higher (so difficulty can be easier for testing) ***)
      end;
    initblocktree();
    Printf.printf "Loading wallet\n"; flush stdout;
    Commands.load_wallet();
    let dur = open_in_bin "/dev/urandom" in (*** this is to compute a nonce for the node to prevent self conns; it doesn't need to be cryptographically secure ***)
    let (n,_) = sei_int64 seic (dur,None) in
    close_in dur;
    this_nodes_nonce := n;
    Printf.fprintf !log "Nonce: %Ld\n" n; flush !log
  end;;

initialize();;
initnetwork();;
if !Config.staking then stkth := Some(Thread.create stakingthread ());;
while true do
  try
    Printf.printf "%s" !Config.prompt; flush stdout;
    let l = read_line() in
    do_command l
  with
  | Exit -> () (*** silently ignore ***)
  | End_of_file -> closelog(); exit 0
  | Failure(x) ->
      Printf.fprintf stdout "Ignoring Uncaught Failure: %s\n" x; flush stdout
  | exn -> (*** unexpected ***)
      Printf.fprintf stdout "Ignoring Uncaught Exception: %s\n" (Printexc.to_string exn); flush stdout
done
