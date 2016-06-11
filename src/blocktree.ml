(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Utils
open Ser
open Hashaux
open Hash
open Net
open Db
open Assets
open Signat
open Tx
open Ctre
open Block

(*** recentblockheaders: associate block header hash with block height and block header ***)
(*** recentblockdeltahs: associate block header hash with a blockdeltah (summarizing stxs by hashvals) ***)
(*** recentblockdeltas: associate block header hash with a blockdelta (with all stxs explicit) ***)
(*** recentstxs: associate hashes of txs/stxs with stxs (may or may not be in blocks) ***)
let recentblockheaders : (hashval * (big_int * int64 * blockheader)) list ref = ref [] (*** ordered by cumulative stake ***)
let recentorphanblockheaders : (hashval * (int64 * blockheader)) list ref = ref []
let recentearlyblockheaders : (hashval * (big_int * int64 * blockheader)) list ref = ref []
let recentcommitments : (int64 * hashval) list ref = ref []
let recentblockdeltahs : (hashval, blockdeltah) Hashtbl.t = Hashtbl.create 1024
let recentblockdeltas : (hashval, blockdelta) Hashtbl.t = Hashtbl.create 1024
let recentstxs : (hashval, stx) Hashtbl.t = Hashtbl.create 65536

let waitingblock : (int64 * int64 * hashval * blockheader * blockdelta * big_int) option ref = ref None;;

let rec insertnewblockheader_real bhh cs mine blkh bh l =
  match l with
  | (bhh1,(_,_,bh1))::r when bhh = bhh1 -> l (*** already in the list ***)
  | (bhh1,(cs1,blkh1,bh1))::r when lt_big_int cs1 cs || (mine && eq_big_int cs1 cs) -> (bhh,(cs,blkh,bh))::l (*** consider the ones this process has created preferable to others with the same cumulative stake ***)
  | x::r -> x::insertnewblockheader_real bhh cs mine blkh bh r
  | [] -> [(bhh,(cs,blkh,bh))]

let insertnewblockheader bhh cs mine blkh bh =
  recentblockheaders := insertnewblockheader_real bhh cs mine blkh bh !recentblockheaders;
  Printf.printf "After insertnewblockheader\n";
  List.iter
    (fun (bhh1,(cs1,blkh1,bh1)) ->
      Printf.printf "%Ld %s cs: %s timestamp %Ld\n" blkh1 (hashval_hexstring bhh1) (string_of_big_int cs1) (let (bhd1,_) = bh1 in bhd1.timestamp)
      )
    !recentblockheaders;
  flush stdout

let known_blockheader_p blkh h =
  List.mem_assoc h !recentblockheaders (*** should also check if it's in a file ***)

let known_blockdeltah_p blkh h =
  Hashtbl.mem recentblockdeltahs h (*** should also check if it's in a file ***)

let known_blockdelta_p blkh h =
  Hashtbl.mem recentblockdeltas h (*** should also check if it's in a file ***)

let known_stx_p h =
  Hashtbl.mem recentstxs h (*** should also check if it's in a file ***)

(*** This is only approximate; it takes the height of a recent block header with the highest cumul stake ***)
let current_block_height () =
  match !recentblockheaders with
  | (_,(_,blkh,_))::_ -> blkh
  | [] -> 0L

let send_initial_inv sout cs =
  let tosend = ref [] in
  let cnt = ref 0 in
  List.iter (fun (bhh,(cumulstk,blkh,bh)) ->
    incr cnt;
    if !cnt < 50000 then
      begin
	tosend := (1,blkh,bhh)::!tosend;
	if Hashtbl.mem recentblockdeltahs bhh then (incr cnt; if !cnt < 50000 then tosend := (2,blkh,bhh)::!tosend);
	if Hashtbl.mem recentblockdeltas bhh then (incr cnt; if !cnt < 50000 then tosend := (3,blkh,bhh)::!tosend);
      end)
    !recentblockheaders;
  Hashtbl.iter (fun txh _ -> incr cnt; if !cnt < 50000 then tosend := (4,0L,txh)::!tosend) recentstxs;
(*
  if not (!tosend = []) then ignore (send_msg sout (Inv(!tosend)));
*)
  cs.sentinv <- List.map (fun (k,_,h) -> (k,h)) !tosend

let extra_inv_h invl mblkh =
  let invr = ref invl in
  let cnt = ref 0 in
  List.iter (fun (bhh,(cumulstk,blkh,bh)) ->
    incr cnt;
    if !cnt < 50000 && blkh >= mblkh && not (List.mem (1,blkh,bhh) !invr) then
      invr := (1,blkh,bhh)::!invr)
    !recentblockheaders;
  !invr

let lastbroadcastextra = ref (Unix.time());;

(*** extra_inv is a function that adds extra inventory to inventory messages to make certain block headers propagate ***)
let extra_inv invl =
  let tm = Unix.time() in
  if tm -. !lastbroadcastextra > 5400.0 then (*** every 90 minutes or so, send a big inv broadcast including the last 256 headers or so ***)
    begin
      lastbroadcastextra := tm;
      extra_inv_h invl (Int64.sub (current_block_height()) 256L)
    end
  else (*** otherwise also send the past 8 headers or so ***)
    extra_inv_h invl (Int64.sub (current_block_height()) 8L)

let broadcast_inv invl =
  let invl = extra_inv invl in
  if not (invl = []) then
    let invl2 = List.map (fun (k,_,h) -> (k,h)) invl in
    List.iter
      (fun (cth,(s,sin,sout,gcs)) ->
	try
	  match !gcs with
	  | Some(cs) ->
	      if not (cs.locked) then
		begin
(*** should acquire a lock on cs.locked, or there could be a race condition with cth ***)
		  cs.locked <- true;
(*
		  ignore (send_msg sout (Inv(invl)));
*)
		  cs.locked <- false;
(*** should now give up lock on cs.locked ***)
		  cs.sentinv <- invl2 @ cs.sentinv
		end
	  | _ -> ()
	with _ -> ())
      !netconns

let stxpool : (hashval,stx) Hashtbl.t = Hashtbl.create 1000;;
let published_stx : (hashval,unit) Hashtbl.t = Hashtbl.create 1000;;
let thytree : (hashval,Mathdata.ttree) Hashtbl.t = Hashtbl.create 1000;;
let sigtree : (hashval,Mathdata.stree) Hashtbl.t = Hashtbl.create 1000;;

type validationstatus = Waiting of float | Valid | Invalid

type blocktree = BlocktreeNode of blocktree option * hashval list ref * hashval option * hashval option * hashval option * hashval * targetinfo * int64 * big_int * int64 * validationstatus ref * bool ref * (hashval * blocktree) list ref

let genesisblocktreenode = ref (BlocktreeNode(None,ref [],None,None,None,!genesisledgerroot,(!genesiscurrentstakemod,!genesisfuturestakemod,!genesistarget),!genesistimestamp,zero_big_int,1L,ref Valid,ref false,ref []));;

let lastcheckpointnode = ref !genesisblocktreenode;;

let bestnode = ref !genesisblocktreenode;;

let node_recent_stakers n =
  let BlocktreeNode(_,rs,_,_,_,_,_,_,_,_,_,_,_) = n in
  !rs

let node_prevblockhash n =
  let BlocktreeNode(_,_,pbh,_,_,_,_,_,_,_,_,_,_) = n in
  pbh

let node_theoryroot n =
  let BlocktreeNode(_,_,_,tr,_,_,_,_,_,_,_,_,_) = n in
  tr

let node_signaroot n =
  let BlocktreeNode(_,_,_,_,sr,_,_,_,_,_,_,_,_) = n in
  sr

let node_ledgerroot n =
  let BlocktreeNode(_,_,_,_,_,lr,_,_,_,_,_,_,_) = n in
  lr

let node_targetinfo n =
  let BlocktreeNode(_,_,_,_,_,_,ti,_,_,_,_,_,_) = n in
  ti

let node_timestamp n =
  let BlocktreeNode(_,_,_,_,_,_,_,tm,_,_,_,_,_) = n in
  tm

let node_cumulstk n =
  let BlocktreeNode(_,_,_,_,_,_,_,_,cs,_,_,_,_) = n in
  cs

let node_children_ref n =
  let BlocktreeNode(_,_,_,_,_,_,_,_,_,_,_,_,chr) = n in
  chr

let print_best_node () =
  let BlocktreeNode(_,_,pbh,_,_,_,_,_,_,_,_,_,_) = !bestnode in
  match pbh with
  | Some(h) -> Printf.fprintf !log "bestnode pbh %s\n" (hashval_hexstring h); flush !log
  | None -> Printf.fprintf !log "bestnode pbh (genesis)\n"; flush !log

let eq_node n1 n2 = node_prevblockhash n1 = node_prevblockhash n2

let blkheaders : (hashval,unit) Hashtbl.t = Hashtbl.create 1000;;
let blkheadernode : (hashval option,blocktree) Hashtbl.t = Hashtbl.create 1000;;
let orphanblkheaders : (hashval option,blockheader) Hashtbl.t = Hashtbl.create 1000;;
let earlyblocktreenodes : (int64 * blocktree) list ref = ref [];;
let tovalidatelist : (validationstatus ref * (unit -> unit)) list ref = ref [];;

let initblocktree () =
  genesisblocktreenode := BlocktreeNode(None,ref [],None,None,None,!genesisledgerroot,(!genesiscurrentstakemod,!genesisfuturestakemod,!genesistarget),!genesistimestamp,zero_big_int,1L,ref Valid,ref false,ref []);
  lastcheckpointnode := !genesisblocktreenode;
  bestnode := !genesisblocktreenode;
  Hashtbl.add blkheadernode None !genesisblocktreenode

let known_thytree_p thyroot =
  match thyroot with
  | None -> true
  | Some(r) -> Hashtbl.mem thytree r

let known_sigtree_p sigroot =
  match sigroot with
  | None -> true
  | Some(r) -> Hashtbl.mem sigtree r

let lookup_thytree thyroot =
  match thyroot with
  | None -> None
  | Some(r) -> Some(Hashtbl.find thytree r)

let lookup_sigtree sigroot =
  match sigroot with
  | None -> None
  | Some(r) -> Some(Hashtbl.find sigtree r)

let add_thytree thyroot otht =
  match thyroot,otht with
  | Some(r),Some(tht) -> if not (Hashtbl.mem thytree r) then Hashtbl.add thytree r tht
  | _,_ -> ()

let add_sigtree sigroot osigt =
  match sigroot,osigt with
  | Some(r),Some(sigt) -> if not (Hashtbl.mem sigtree r) then Hashtbl.add sigtree r sigt
  | _,_ -> ()

let rec insertnewdelayed (tm,n) btnl =
  match btnl with
  | [] -> [(tm,n)]
  | (tm2,n2)::btnr when tm < tm2 -> (tm,n)::btnl
  | (tm2,n2)::btnr -> (tm2,n2)::insertnewdelayed (tm,n) btnr

let setsigpipeignore () =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;;

let process_new_tx h hh =
  try
    let tx1 = DbTx.dbget h in
    let txid = hashtx tx1 in
    if not (txid = h) then (*** wrong hash, remove it but don't blacklist the (wrong) hashval ***)
      begin
        Printf.fprintf !log "WARNING: Received tx with different hash as advertised, removing %s\nThis may be due to a bug or due to a misbehaving peer.\n" hh; flush !log;
	DbTx.dbdelete h;
	DbTxSignatures.dbdelete h;
      end
    else if tx_valid tx1 then
      begin (*** checking the validity of signatures and support depend on the current ledger; delay this here in favor of checking them before including them in a block we're actively trying to stake; note that the relevant properties are checked when they are included in a block as part of checking a block is valid ***)
	let txsigs1 = DbTxSignatures.dbget h in
        Hashtbl.add stxpool txid (tx1,txsigs1);
      end
    else
      (*** in this case, reject the tx since it's definitely not valid ***)
     begin
       DbBlacklist.dbput h true;
       DbTx.dbdelete h;
       DbTxSignatures.dbdelete h;
     end
  with (*** in some cases, failure should lead to blacklist and removal of the tx, but it's not clear which cases; if it's in a block we might need to distinguish between definitely incorrect vs. possibly incorrect ***)
  | Not_found ->
      Printf.fprintf !log "Problem with tx, deleting it\n"; flush !log;
      DbTx.dbdelete h;
      DbTxSignatures.dbdelete h;
  | e ->
      Printf.fprintf !log "exception %s\n" (Printexc.to_string e); flush !log;
      ()

let rec processdelayednodes tm btnl =
  match btnl with
  | (tm2,n2)::btnr when tm2 <= tm ->
    let BlocktreeNode(_,_,_,_,_,_,_,_,bestcumulstk,_,_,_,_) = !bestnode in
    let BlocktreeNode(_,_,pbh,_,_,_,_,_,newcumulstk,_,_,_,_) = n2 in
    if gt_big_int newcumulstk bestcumulstk then
      begin
        Printf.fprintf !log "New best blockheader %s\n" (match pbh with Some(h) -> hashval_hexstring h | None -> "(genesis)"); flush !log;
        bestnode := n2
      end;
    processdelayednodes tm btnr
  | _ -> btnl

let rec processblockvalidation vl =
  match vl with
  | [] -> []
  | (v,f)::vr ->
      let vr2 = processblockvalidation vr in
      f();
      match !v with
      | Waiting(_) -> (v,f)::vr2
      | _ -> vr2

let add_to_validheaders_file h =
  let fn = Filename.concat (datadir()) "validheaders" in
  let f = open_out_gen [Open_append;Open_creat] 0o664 fn in
  output_string f (h ^ "\n");
  close_out f

let add_to_headers_file h =
  let fn = Filename.concat (datadir()) "headers" in
  let f = open_out_gen [Open_append;Open_creat] 0o664 fn in
  output_string f (h ^ "\n");
  close_out f

let rec is_recent_staker stkaddr n i =
  if i > 0 then
    begin
      let BlocktreeNode(par,stakers,_,_,_,_,_,_,_,_,_,_,_) = n in
      if List.mem stkaddr !stakers then
	true
      else
	match par with
	| Some(p) -> is_recent_staker stkaddr p (i-1)
	| _ -> false
    end
  else
    false

let rec record_recent_staker stkaddr n i =
  if i > 0 then
    begin
      let BlocktreeNode(par,stakers,_,_,_,_,_,_,_,_,_,_,_) = n in
      stakers := stkaddr::!stakers;
      match par with
      | Some(p) -> record_recent_staker stkaddr p (i-1)
      | None -> ()
    end

let equ_tinfo (x,(y3,y2,y1,y0),z) (u,(v3,v2,v1,v0),w) =
   x = u && y3 = v3 && y2 = v2 && y1 = v1 && Int64.logand y0 (Int64.lognot 1L) = Int64.logand v0 (Int64.lognot 1L) && eq_big_int z w

let rec process_new_header_a h hh blkh1 blkhd1 initialization knownvalid =
  let prevblkh = blkhd1.prevblockhash in
  begin
    try
      let prevnode = Hashtbl.find blkheadernode prevblkh in
      let BlocktreeNode(_,_,_,thyroot,sigroot,ledgerroot,currtinfo,tmstamp,prevcumulstk,blkhght,validated,blacklisted,succl) = prevnode in
      if !blacklisted then (*** child of a blacklisted node, drop and blacklist it ***)
        begin
	  DbBlacklist.dbput h true;
	  DbBlockHeader.dbdelete h;
        end
      else if
	valid_blockheader blkhght currtinfo blkh1
          && 
	blockheader_succ_a (Int64.to_int32 (Int64.sub blkhd1.timestamp tmstamp)) tmstamp currtinfo blkh1
      then
	begin
          Hashtbl.add blkheaders h ();
(*** (*** todo: relay ***)
	  let qednetch = Unix.open_process_in ((qednetd()) ^ " relaydata qblockheader " ^ h) in
	  ignore (Unix.close_process_in qednetch);
***)
          let (csm1,fsm1,tar1) = blkhd1.tinfo in
	  let csm2 = stakemod_pushbit (stakemod_lastbit fsm1) csm1 in
	  let fsm2 = stakemod_pushbit false fsm1 in (** the new bit doesn't matter here **)
	  let tar2 = retarget tar1 blkhd1.deltatime in
          let newcumulstake = cumul_stake prevcumulstk tar1 blkhd1.deltatime in
	  let validated = ref (if knownvalid then Valid else Waiting(Unix.time())) in
          let newnode = BlocktreeNode(Some(prevnode),ref [blkhd1.stakeaddr],Some(h),blkhd1.newtheoryroot,blkhd1.newsignaroot,blkhd1.newledgerroot,(csm2,fsm2,tar2),blkhd1.timestamp,newcumulstake,Int64.add blkhght 1L,validated,ref false,ref []) in
	  (*** add it as a leaf, indicate that we want the block delta to validate it, and check if it's the best ***)
	  Hashtbl.add blkheadernode (Some(h)) newnode;
          succl := (h,newnode)::!succl;
	  record_recent_staker blkhd1.stakeaddr prevnode 6;
	  let validatefn () =
	    try
	      let blkdh = DbBlockDeltaH.dbget h in
	      let (stkout,forf,cg,txhl) = blkdh in
	      let alltxs = ref true in
	      List.iter
		(fun txh ->
		  if not (Hashtbl.mem stxpool txh) then
		    begin
		      alltxs := false;
(*** (*** todo: request tx ***)
		      let qednetch = Unix.open_process_in ((qednetd()) ^ " getdata qtx " ^ (hashval_hexstring txh)) in
		      ignore (Unix.close_process_in qednetch);
***)
		    end)
		txhl;
	      if !alltxs then
		let blkdel = { stakeoutput = stkout;
			       forfeiture = forf;
			       prevledgergraft = cg;
			       blockdelta_stxl = List.map (fun txh -> Hashtbl.find stxpool txh) txhl
			     }
		in
		let blk = (blkh1,blkdel) in
		if known_thytree_p thyroot && known_sigtree_p sigroot then (*** these should both be known if the parent block has been validated ***)
		  if valid_block (lookup_thytree thyroot) (lookup_sigtree sigroot) blkhght blkhd1.tinfo blk then
		    begin (*** if valid_block succeeds, then latesttht and latestsigt will be set to the transformed theory tree and signature tree ***)
		      validated := Valid;
		      if not initialization then add_to_validheaders_file hh;
                      let BlocktreeNode(_,_,_,_,_,_,_,_,bestcumulstk,_,_,_,_) = !bestnode in
		      if gt_big_int newcumulstake bestcumulstk then bestnode := newnode;
		      add_thytree blkhd1.newtheoryroot !latesttht;
		      add_sigtree blkhd1.newsignaroot !latestsigt;
(*** (** todo: relay **)
		      let qednetch = Unix.open_process_in ((qednetd()) ^ " relaydata qblockdeltah " ^ h) in
		      ignore (Unix.close_process_in qednetch);
***)
		      (*** construct a transformed tree consisting of elements ***)
		      let prevc = load_expanded_ctree (ctree_of_block blk) in
		      match txl_octree_trans blkhght (txl_of_block blk) (Some(prevc)) with
		      | Some(newc) -> ignore (save_ctree_elements newc)
                      | None -> raise (Failure("transformed tree was empty, although block seemed to be valid"))
		    end
		  else
		    begin
		      validated := Invalid; (*** could delete and possibly blacklist the qblockdeltah, but will leave it for now ***)
		    end
	    with
	    | Not_found -> (*** request blockdeltah h from peers ***)
		()
(***
	      let qednetch = Unix.open_process_in ((qednetd()) ^ " getdata qblockdeltah " ^ h) in
	      ignore (Unix.close_process_in qednetch);
***)
	  in
	  tovalidatelist := (validated,validatefn)::!tovalidatelist;
          if not initialization then add_to_headers_file hh;
          if Int64.of_float (Unix.time()) < tmstamp then (*** delay it ***)
            earlyblocktreenodes := insertnewdelayed (tmstamp,newnode) !earlyblocktreenodes
          else
            let BlocktreeNode(_,_,_,_,_,_,_,_,bestcumulstk,_,_,_,_) = !bestnode in
            if gt_big_int newcumulstake bestcumulstk then
	      begin
                Printf.fprintf !log "New best blockheader %s\n" hh; flush !log;
                bestnode := newnode
	      end;
            List.iter
              (fun blkh1 -> let (blkhd1,_) = blkh1 in let h = hash_blockheaderdata blkhd1 in process_new_header_a h (hashval_hexstring h) blkh1 blkhd1 initialization knownvalid)
              (Hashtbl.find_all orphanblkheaders (Some(h)))
        end
      else
        begin (*** if it's wrong, delete it and blacklist it so it won't look new in the future ***)
	  DbBlacklist.dbput h true;
	  DbBlockHeader.dbdelete h;
        end
    with Not_found -> (*** orphan block header, put it on the relevant hash table and request parent ***)
      Hashtbl.add orphanblkheaders prevblkh blkh1;
      match prevblkh with
      | Some(pbh) ->
	  if DbBlockHeader.dbexists pbh then
	    process_new_header pbh (hashval_hexstring pbh) initialization knownvalid
	  else
	    (*** todo: request qblockheader pbh ***)
	    ()
      | None -> ()
  end
and process_new_header_b h hh initialization knownvalid =
  Printf.fprintf !log "Processing new header %s\n" hh; flush !log;
  try
    let blkh1 = DbBlockHeader.dbget h in
    let (blkhd1,blkhs1) = blkh1 in
    if not (hash_blockheaderdata blkhd1 = h) then (*** wrong hash, remove it but don't blacklist the (wrong) hashval ***)
      begin
        Printf.fprintf !log "WARNING: Received block header with different hash as advertised, removing %s\nThis may be due to a bug or due to a misbehaving peer.\n" hh; flush !log;
	DbBlockHeader.dbdelete h
      end
    else
      process_new_header_a h hh blkh1 blkhd1 initialization knownvalid
  with (*** in some cases, failure should lead to blacklist and removal of the header, but it's not clear which cases; if it's in a block we might need to distinguish between definitely incorrect vs. possibly incorrect ***)
  | Not_found ->
      Printf.fprintf !log "Problem with blockheader %s, deleting it\n" hh; flush !log;
      DbBlockHeader.dbdelete h
  | e ->
      Printf.fprintf !log "exception %s\n" (Printexc.to_string e); flush !log;
      ()
and process_new_header h hh initialization knownvalid =
  if not (Hashtbl.mem blkheaders h) then
    process_new_header_b h hh initialization knownvalid

let init_headers_a fn knownvalid =
  if Sys.file_exists fn then
    let f = open_in fn in
    begin
      try
        while true do
          let h = input_line f in
          process_new_header (hexstring_hashval h) h true knownvalid
        done
      with End_of_file -> close_in f
    end
  else
    ()

let init_headers () =
  init_headers_a (Filename.concat (datadir()) "validheaders") true;
  init_headers_a (Filename.concat (datadir()) "headers") false

let rec find_best_validated_block_from fromnode bestcumulstk =
  let BlocktreeNode(_,_,_,_,_,_,_,_,cumulstk,_,validatedp,blklistp,succl) = fromnode in
  if not !blklistp && !validatedp = Valid then
    begin
      let newbestcumulstk = ref
	(if gt_big_int cumulstk bestcumulstk then
	  begin
	    bestnode := fromnode;
	    cumulstk
	  end
	else
	  bestcumulstk)
      in
      List.iter
	(fun (_,childnode) ->
	  newbestcumulstk := find_best_validated_block_from childnode !newbestcumulstk)
	!succl;
      !newbestcumulstk
    end
  else
    bestcumulstk

let publish_stx txh stx1 =
  let (tx1,txsigs1) = stx1 in
  DbTx.dbput txh tx1;
  DbTxSignatures.dbput txh txsigs1;
  Hashtbl.add published_stx txh ()

let publish_block bhh (bh,bd) =
  DbBlockHeader.dbput bhh bh;
  (*** todo: relay bh ***)
  let stxhl =
    List.map
      (fun (tx1,txsg1) ->
	let tx1h = hashtx tx1 in
	if not (Hashtbl.mem published_stx tx1h) then publish_stx tx1h (tx1,txsg1);
	tx1h)
      bd.blockdelta_stxl
  in
  let bdh = (bd.stakeoutput,bd.forfeiture,bd.prevledgergraft,stxhl) in
  DbBlockHeader.dbput bhh bh;
  DbBlockDeltaH.dbput bhh bdh;
  (*** todo: relay bdh ***)
  ()

let qednetmain initfn preloopfn =
  setsigpipeignore();
  Printf.fprintf !log "Starting networking\n"; flush !log;
  Printf.fprintf !log "Init headers\n"; flush !log;
  init_headers();
  initfn();
  Printf.fprintf !log "Initialization phase complete.\n"; flush !log;
  while true do
      preloopfn();
      earlyblocktreenodes := processdelayednodes (Int64.of_float (Unix.time())) !earlyblocktreenodes;
      tovalidatelist := processblockvalidation !tovalidatelist;
(***
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 1.0 });
      let l = input_line qednetch3 in
      ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = 0.0 });
      let ll = String.length l in
      if ll = 68 && String.sub l 0 4 = "QTX:" then
	let hh = String.sub l 28 40 in
	process_new_tx (hexstring_hashval hh) hh
      else if ll = 72 && String.sub l 0 8 = "QHEADER:" then
	let hh = String.sub l 32 40 in
	process_new_header (hexstring_hashval hh) hh false false
***)
  done

