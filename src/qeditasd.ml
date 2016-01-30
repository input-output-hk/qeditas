(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int;;
open Ser;;
open Hash;;
open Secp256k1;;
open Signat;;
open Assets;;
open Tx;;
open Ctre;;
open Ctregraft;;
open Block;;
open Net;;
open Setconfig;;

let currstaking : (int64 * big_int * hashval * blocktree * (stakemod * stakemod * big_int)) option ref = ref None;;
let waitingblock : (int64 * int64 * hashval * blockheader * blockdelta * big_int * blocktree) option ref = ref None;;

let compute_recid (r,s) k =
  match smulp k _g with
  | Some(x,y) ->
      if eq_big_int x r then
	if evenp y then 0 else 1
      else
	if evenp y then 2 else 3
  | None -> raise (Failure "bad0");;

let stakingproccomm : (in_channel * out_channel * in_channel) option ref = ref None;;

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

let send_assets_to_staker tostkr c n =
  let reasontostake = ref false in
  List.iter
    (fun (k,b,(x,y),w,h,alpha) ->
      Printf.printf "about to get assets from %s for staking\n" alpha; flush stdout;
      if not (is_recent_staker h n 6) then
	match ctree_addr (hashval_p2pkh_addr h) c None with
	| (Some(hl),_) ->
	    reasontostake := true;
	    hlist_insertstakingassets tostkr h (nehlist_hlist hl)
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
	      reasontostake := true;
	      hlist_insertstakingassets tostkr (x4,x3,x2,x1,x0) (nehlist_hlist hl)
	  | _ -> ())
    !Commands.walletendorsements;
  flush tostkr;
  !reasontostake;;

let stop_staking () =
  match !stakingproccomm with
  | Some(sti,sto,ste) ->
      begin
	try
	  output_byte sto 80;
	  flush sto;
	  ignore (Unix.close_process_full (sti,sto,ste))
	with _ ->
	  ignore (Unix.close_process_full (sti,sto,ste))
      end;
      stakingproccomm := None;
      currstaking := None
  | None -> ();;

let waitingonvalidationsince = ref None;;

let start_staking () =
  stop_staking(); (*** stop staking first, if necessary ***)
  let stkexec = Filename.concat (Filename.dirname (Sys.argv.(0))) "qeditasstk" in
  let stkexec = if !Config.testnet then (stkexec ^ " -testnet=1") else stkexec in
  try
    let best = !bestnode in
    let BlocktreeNode(_,_,prevblkh,thyroot,sigroot,currledgerroot,tinfo,deltm,tmstamp,prevcumulstk,blkhght,validated,blacklisted,succl) = best in
    if !blacklisted || !validated = Some(false) then
      ignore (find_best_validated_block_from !lastcheckpointnode zero_big_int)
    else if !validated = None then
      begin
	match !waitingonvalidationsince with
	| None -> waitingonvalidationsince := Some(Unix.time())
	| Some(tm) ->
	    if Unix.time() > tm +. 60.0 then
	      begin (*** give up and switch to staking on best validated node ***)
		waitingonvalidationsince := None;
		ignore (find_best_validated_block_from !lastcheckpointnode zero_big_int)
	      end
      end
    else
      begin
	Printf.printf "should stake on top of current best block, height %Ld, hash %s\n" blkhght (match prevblkh with Some(bh) -> (hashval_hexstring bh) | None -> "(genesis)"); flush stdout;
	let (fromstkr,tostkr,stkerr) = Unix.open_process_full stkexec [||] in
	stakingproccomm := Some(fromstkr,tostkr,stkerr);
	Commands.stakingassets := [];
	if send_assets_to_staker tostkr (CHash(currledgerroot)) best then
	  let (csm1,fsm1,tar1) = tinfo in
	  begin
	    output_byte tostkr 66; (*** send the staking process the block height, the target, the stake modifier and the next allowed timestamp ***)
	    seocf (seo_int64 seoc blkhght (tostkr,None));
	    seocf (seo_big_int_256 seoc tar1 (tostkr,None));
	    seocf (seo_stakemod seoc csm1 (tostkr,None));
	    output_byte tostkr 116;
	    seocf (seo_int64 seoc (Int64.add 1L tmstamp) (tostkr,None));
	    output_byte tostkr 83; (*** start staking ***)
	    flush tostkr;
	    Printf.printf "staking on top of current best block, height %Ld, hash %s\n" blkhght (match prevblkh with Some(bh) -> (hashval_hexstring bh) | None -> "(genesis)"); flush stdout;
	    currstaking := Some(blkhght,prevcumulstk,currledgerroot,best,(csm1,fsm1,tar1))
	  end
	else
	  begin
	    Printf.printf "No wallet assets to stake in the current ctree. Not staking at the moment.\n";
	    flush stdout;
	    stop_staking()
	  end
      end
  with
  | GettingRemoteData ->
      Printf.printf "Before staking, requesting required info from peers\n"; flush stdout;
  | Not_found -> ()
  | exc -> Printf.printf "raised: %s\n" (Printexc.to_string exc); flush stdout;;

let randbyte = ref None;;

let rand_bit() =
  match !randbyte with
  | Some(x,i) ->
      if i > 0 then
	randbyte := Some(x,i-1)
      else
	randbyte := None;
      (x lsr i) land 1 = 1
  | None ->
      let r = open_in_bin "/dev/random" in
      let x = input_byte r in
      randbyte := Some(x,6);
      close_in r;
      x lsr 7 = 1

let rand_256() =
  let r = open_in_bin "/dev/random" in
  let v = ref zero_big_int in
  for i = 0 to 31 do
    let x = input_byte r in
    v := add_int_big_int x (shift_left_big_int !v 8)
  done;
  close_in r;
  !v

let main () =
  begin
    datadir_from_command_line(); (*** if -datadir=... is on the command line, then set Config.datadir so we can find the config file ***)
    process_config_file();
    process_config_args(); (*** settings on the command line shadow those in the config file ***)
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
	max_target := shift_left_big_int unit_big_int 255; (*** make the max_target much higher (so difficulty can be easier for testing) ***)
	genesistarget := shift_left_big_int unit_big_int 248; (*** make the genesistarget much higher (so difficulty can be easier for testing) ***)
      end;
    Printf.printf "Loading wallet\n"; flush stdout;
    Commands.load_wallet();
    let initfn () = () in
    let preloopfn () =
      if !Config.staking then
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
		    let alpha2 = hashval_p2pkh_addr alpha in
		    let (aid,_) = sei_hashval seic c in
		    Printf.printf "Asset %s at address %s can stake at time %Ld (%Ld seconds from now)\n" (hashval_hexstring aid) (Cryptocurr.addr_qedaddrstr alpha2) stktm (Int64.sub stktm (Int64.of_float (Unix.time())));
		    flush stdout;
		    begin
		      try
			let (_,_,bday,obl,v) = List.find (fun (_,h,_,_,_) -> h = aid) !Commands.stakingassets in
			match !currstaking with
			| Some(blkh,cs,prevledgerroot,n,(csm1,fsm1,tar1)) ->
Printf.printf "h1\n"; flush stdout;
			    stop_staking();
Printf.printf "h2\n"; flush stdout;
			    if check_hit_b blkh bday obl v csm1 tar1 stktm aid alpha None then (*** confirm the staking process is correct ***)
			      let BlocktreeNode(_,_,pbhh,pbthyroot,pbsigroot,_,pbtinfo,pbdeltm,pbtmstamp,cs,blkhght,_,_,_) = n in
			      let deltm = Int64.to_int32 (Int64.sub stktm pbtmstamp) in
			      let newrandbit = rand_bit() in
Printf.printf "h3\n"; flush stdout;
			      let csm2 = stakemod_pushbit (stakemod_lastbit fsm1) csm1 in
			      let fsm2 = stakemod_pushbit newrandbit fsm1 in
			      let tar2 = retarget tar1 deltm in
Printf.printf "h4\n"; flush stdout;
			      let stkoutl = [(alpha2,(None,Currency(v)));(alpha2,(Some(p2pkhaddr_payaddr alpha,Int64.add blkh (reward_locktime blkh),true),Currency(rewfn blkh)))] in
			      let coinstk : tx = ([(alpha2,aid)],stkoutl) in
			      let prevc = Some(CHash(prevledgerroot)) in
			      let octree_ctree c =
				match c with
				| Some(c) -> c
				| None -> raise (Failure "tree should not be empty")
			      in
Printf.printf "h5\n"; flush stdout;
			      let dync = ref (octree_ctree (tx_octree_trans blkh coinstk prevc)) in
			      let otherstxs = ref [] in
			      Hashtbl.iter
				(fun h ((tauin,tauout),sg) ->
				  Printf.printf "Trying to include tx %s\n" (hashval_hexstring h); flush stdout;
				  if tx_valid (tauin,tauout) then
				    try
				      Printf.printf "tx valid\n"; flush stdout;
				      let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets tauin !dync) in
				      Printf.printf "found input assets\n"; flush stdout;
				      if tx_signatures_valid blkh al ((tauin,tauout),sg) then
					begin
					  Printf.printf "signatures valid\n"; flush stdout;
					  if ctree_supports_tx None None blkh (tauin,tauout) !dync >= 0L then
					    begin
					      Printf.printf "ctree supports tx\n"; flush stdout;
					      let c = octree_ctree (tx_octree_trans blkh (tauin,tauout) (Some(!dync))) in
					      Printf.printf "transformed ctree\n"; flush stdout;
					      otherstxs := ((tauin,tauout),sg)::!otherstxs;
					      dync := c
					    end
					end
				    with _ -> ())
				Commands.txpool;
			      otherstxs := List.rev !otherstxs;
			      let othertxs = List.map (fun (tau,_) -> tau) !otherstxs in
			      let prevcforblock =
				match
				  get_txl_supporting_octree (coinstk::othertxs) prevc
				with
				| Some(c) -> c
				| None -> raise (Failure "ctree should not have become empty")
			      in
			      let (prevcforheader,cgr) = factor_inputs_ctree_cgraft [(alpha2,aid)] prevcforblock in
			      let newcr = save_ctree_elements !dync in
			      let bhdnew : blockheaderdata
				  = { prevblockhash = pbhh;
				      newtheoryroot = None; (*** leave this as None for now ***)
				      newsignaroot = None; (*** leave this as None for now ***)
				      newledgerroot = newcr;
				      stakeaddr = alpha;
				      stakeassetid = aid;
				      stored = None;
				      timestamp = stktm;
				      deltatime = deltm;
				      tinfo = (csm2,fsm2,tar2);
				      prevledger = prevcforheader
				    }
			      in
			      let bhdnewh = hash_blockheaderdata bhdnew in
			      let bhsnew =
				try
				  let (prvk,b,_,_,_,_) = List.find (fun (_,_,_,_,beta,_) -> beta = alpha) !Commands.walletkeys in
				  let r = rand_256() in
				  let sg : signat = signat_hashval bhdnewh prvk r in
				  { blocksignat = sg;
				    blocksignatrecid = compute_recid sg r;
				    blocksignatfcomp = b;
				    blocksignatendorsement = None
				  }
				with Not_found ->
				  try
				    let (_,beta,(w,z),recid,fcomp,esg) =
				      List.find
					(fun (alpha2,beta,(w,z),recid,fcomp,esg) ->
					  let (p,x0,x1,x2,x3,x4) = alpha2 in
					  let (q,_,_,_,_,_) = beta in
					  not p && (x0,x1,x2,x3,x4) = alpha && not q)
					!Commands.walletendorsements
				    in
				    let (_,x0,x1,x2,x3,x4) = beta in
				    let betah = (x0,x1,x2,x3,x4) in
				    let (prvk,b,_,_,_,_) =
				      List.find
					(fun (_,_,_,_,beta2,_) -> beta2 = betah)
					!Commands.walletkeys in
				    let r = rand_256() in
				    let sg : signat = signat_hashval bhdnewh prvk r in
				    { blocksignat = sg;
				      blocksignatrecid = compute_recid sg r;
				      blocksignatfcomp = b;
				      blocksignatendorsement = Some(betah,recid,fcomp,esg)
				    }
				  with Not_found ->
				    raise (Failure("Was staking for " ^ Cryptocurr.addr_qedaddrstr (hashval_p2pkh_addr alpha) ^ " but have neither the private key nor an appropriate endorsement for it."))
			      in
			      let bhnew = (bhdnew,bhsnew) in
			      if not (valid_blockheader blkhght bhnew && blockheader_succ_a pbdeltm pbtmstamp pbtinfo bhnew) then
				raise (Failure("Incorrect block header from staking; bug; not publishing it"));
			      Printf.printf "Including %d txs in block\n" (List.length !otherstxs);
			      let forf = None in (*** leave this as None for now; should check for double signing ***)
			      let bdnew : blockdelta =
				{ stakeoutput = stkoutl;
				  forfeiture = forf;
				  prevledgergraft = cgr;
				  blockdelta_stxl = !otherstxs
				}
			      in
			      if not (valid_block (lookup_thytree pbthyroot) (lookup_sigtree pbsigroot) blkhght (bhnew,bdnew)) then
				raise (Failure("Incorrect block from staking; bug; not publishing it"));
			      let csnew = cumul_stake cs tar1 bhdnew.deltatime in
			      waitingblock := Some(stktm,blkhght,bhdnewh,bhnew,bdnew,csnew,n);
			| None -> (*** error, but ignore for now ***)
			    Printf.printf "creating block error\n"; flush stdout;
			    ()
		      with Not_found -> ()
		    end;
		    flush stdout;
		| Some(z) when z = 83 -> (*** hit with storage ***)
		    let c = (fromstkr,None) in
		    let (stktm,c) = sei_int64 seic c in
		    let (alpha,c) = sei_hashval seic c in
		    let (aid,c) = sei_hashval seic c in
		    let (strg,_) = sei_postor seic c in
		    stop_staking();
		    Printf.printf "Found a hit using a stake combined with storage, but the code to handle it isn't written.\n";
		    flush stdout
		| Some(z) -> (*** something has gone wrong. die ***)
		    Printf.printf "The staking process sent back %d which is meaningless.\nKilling staker\n" z;
		    stop_staking();
		| None ->
		    match input_byte_nohang stkerr 0.1 with
		    | Some(z) -> (*** something has gone wrong. die ***)
			Printf.printf "The staking process sent error code %d.\nKilling staker\n" z;
			stop_staking();
		    | None -> ()
	      with
	      | _ ->
		  Printf.printf "Exception thrown while trying to read from the staking process.\nKilling staker\n";
		  stop_staking();
	end;
      if !Config.staking then
	begin (*** check to see if a new block can be published ***)
	  match !waitingblock with
	  | Some(_,_,_,_,_,_,n) when not (eq_node n !bestnode) -> (*** if there's now a better block to stake on than the one the waiting block was staked on, forget it and restart staking ***)
	      waitingblock := None;
	      start_staking();
	  | Some(stktm,blkh,bhh,bh,bd,cs,_) when Int64.of_float (Unix.time()) >= stktm ->
	      publish_block bhh (bh,bd); (*** broadcast the block header, the block deltah and all txs; integrate into the tree ***)
	      waitingblock := None;
	      start_staking(); (*** start staking again ***)
	  | None -> (*** if there is no waiting block and we aren't staking, then restart staking ***)
	      begin
		match !currstaking with
		| None ->
		    start_staking()
		| Some(_,_,_,n,_) -> (*** if we are staking, make sure it's still on top of the best block ***)
Printf.printf "g1\n"; flush stdout;
		    if not (eq_node n !bestnode) then
		      start_staking()
	      end
	  | _ ->
	      ()
	end
    in
    qednetmain initfn preloopfn
  end;;

try
  main ()
with
| Failure(x) ->
    Printf.printf "%s\nExiting.\n" x;
    stop_staking ()
| exn -> (*** unexpected ***)
    Printf.printf "Exception: %s\nExiting.\n" (Printexc.to_string exn);
    stop_staking ();;
