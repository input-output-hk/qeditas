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

let lastcheckpoint : (big_int * int64 * hashval) option ref = ref None;; (*** cumulative stake, block height, blockheaderdata hash ***)
let currstaking : (int64 * big_int * hashval * blocktree * (stakemod * stakemod * big_int)) option ref = ref None;;

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

let send_assets_to_staker tostkr c =
  let reasontostake = ref false in
  List.iter
    (fun (k,b,(x,y),w,h,alpha) ->
      match ctree_addr (hashval_p2pkh_addr h) c with
      | (Some(CLeaf(_,hl)),_) ->
	  reasontostake := true;
	  hlist_insertstakingassets tostkr h (nehlist_hlist hl)
      | _ ->
	  ()
    )
    !Commands.walletkeys;
  List.iter
    (fun (alpha,beta,_,_,_,_) ->
      let (p,x4,x3,x2,x1,x0) = alpha in
      let (q,_,_,_,_,_) = beta in
      if not p && not q then (*** only p2pkh can stake ***)
	begin
	  match ctree_addr (payaddr_addr alpha) c with
	  | (Some(CLeaf(_,hl)),_) ->
	      reasontostake := true;
	      hlist_insertstakingassets tostkr (x4,x3,x2,x1,x0) (nehlist_hlist hl)
	  | _ ->
	      ()		
	end)
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
  try
    let best = !bestnode in
    let BlocktreeNode(prevblkh,thyroot,sigroot,currledgerroot,tinfo,deltm,tmstamp,prevcumulstk,blkhght,validated,blacklisted,succl) = best in
    if !blacklisted || !validated = Some(false) then
      ignore (find_best_validated_block_from !lastcheckpointnode zero_big_int)
    else if !validated = None then
      begin
	match !waitingonvalidationsince with
	| None -> waitingonvalidationsince := Some(Unix.time())
	| Some(tm) ->
	    if Unix.time() > tm +. 60.0 then
	      ignore (find_best_validated_block_from !lastcheckpointnode zero_big_int) (*** give up and switch to staking on best validated node ***)
      end
    else
      begin
	Printf.printf "should stake on top of current best block, height %Ld, hash %s\n" blkhght (match prevblkh with Some(bh) -> (hashval_hexstring bh) | None -> "(genesis)"); flush stdout;
	let ca = lookup_frame_ctree_root_abbrev !localframehash currledgerroot in
	let (fromstkr,tostkr,stkerr) = Unix.open_process_full stkexec [||] in
	stakingproccomm := Some(fromstkr,tostkr,stkerr);
	if send_assets_to_staker tostkr (CAbbrev(currledgerroot,ca)) then
	  let (csm1,fsm1,tar1) = tinfo in
	  let csm2 = stakemod_pushbit (stakemod_lastbit fsm1) csm1 in
	  let tar2 = retarget tar1 deltm in
	  begin
	    output_byte tostkr 66; (*** send the staking process the block height, the target, the stake modifier and the next allowed timestamp ***)
	    seocf (seo_int64 seoc blkhght (tostkr,None));
	    seocf (seo_big_int_256 seoc tar2 (tostkr,None));
	    seocf (seo_stakemod seoc csm2 (tostkr,None));
	    output_byte tostkr 116;
	    seocf (seo_int64 seoc (Int64.add 1L tmstamp) (tostkr,None));
	    output_byte tostkr 83; (*** start staking ***)
	    flush tostkr;
	    Printf.printf "staking on top of current best block, height %Ld, hash %s\n" blkhght (match prevblkh with Some(bh) -> (hashval_hexstring bh) | None -> "(genesis)"); flush stdout;
	    currstaking := Some(blkhght,prevcumulstk,currledgerroot,best,(csm2,fsm1,tar2))
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
    Printf.printf "Loading current frame\n"; flush stdout;
    localframe := Commands.load_currentframe();
    localframehash := hashframe !localframe;
    let initfn () = () in
    let preloopfn () = () in
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
