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

let stxpool : (hashval,stx) Hashtbl.t = Hashtbl.create 1000;;
let published_stx : (hashval,unit) Hashtbl.t = Hashtbl.create 1000;;
let thytree : (hashval,Mathdata.ttree) Hashtbl.t = Hashtbl.create 1000;;
let sigtree : (hashval,Mathdata.stree) Hashtbl.t = Hashtbl.create 1000;;

type validationstatus = Waiting of float | ValidBlock | InvalidBlock

type blocktree = BlocktreeNode of blocktree option * hashval list ref * hashval option * hashval option * hashval option * hashval * targetinfo * int64 * big_int * int64 * validationstatus ref * bool ref * (hashval * blocktree) list ref

let genesisblocktreenode = ref (BlocktreeNode(None,ref [],None,None,None,!genesisledgerroot,(!genesiscurrentstakemod,!genesisfuturestakemod,!genesistarget),!Config.genesistimestamp,zero_big_int,1L,ref ValidBlock,ref false,ref []));;

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

let node_blockheight n =
  let BlocktreeNode(_,_,_,_,_,_,_,_,_,blkh,_,_,_) = n in
  blkh

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
let orphanblkheaders : (hashval option,hashval * blockheader) Hashtbl.t = Hashtbl.create 1000;;
let earlyblocktreenodes : (int64 * blocktree) list ref = ref [];;
let tovalidatelist : (validationstatus ref * (unit -> unit)) list ref = ref [];;

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

let rec collect_inv m cnt tosend n txinv =
  if !cnt < m then
    if !cnt mod 5 = 0 && not (txinv = []) then
      begin
	match txinv with
	| (txid::txinvr) ->
	    tosend := (int_of_msgtype STx,0L,txid)::!tosend; incr cnt;
	    collect_inv m cnt tosend n txinvr
	| [] -> incr cnt; collect_inv m cnt tosend n [] (*** can never happen ***)
      end
    else
      let BlocktreeNode(par,_,pbh,_,_,_,_,_,_,blkh,_,_,_) = n in
      match pbh with
      | None -> ()
      | Some(pbh) ->
	  if DbBlockHeader.dbexists pbh then
	    begin
	      tosend := (int_of_msgtype Headers,blkh,pbh)::!tosend; incr cnt;
	      if DbBlockDelta.dbexists pbh then (tosend := (int_of_msgtype Blockdelta,blkh,pbh)::!tosend; incr cnt)
	    end;
	  match par with
	  | None -> ()
	  | Some(p) -> collect_inv m cnt tosend p txinv

let send_inv m sout cs =
  let cnt = ref 0 in
  let tosend = ref [] in
  let txinv = ref [] in
  Hashtbl.iter (fun k _ -> txinv := k::!txinv) stxpool;
  collect_inv m cnt tosend !bestnode !txinv;
  let invmsg = Buffer.create 10000 in
  let c = ref (seo_int32 seosb (Int32.of_int !cnt) (invmsg,None)) in
  List.iter
    (fun (i,blkh,h) ->
      let cn = seo_prod3 seo_int8 seo_int64 seo_hashval seosb (i,blkh,h) !c in
      c := cn)
    !tosend;
  ignore (queue_msg cs Inv (Buffer.contents invmsg));;

let rec insertnewdelayed (tm,n) btnl =
  match btnl with
  | [] -> [(tm,n)]
  | (tm2,n2)::btnr when tm < tm2 -> (tm,n)::btnl
  | (tm2,n2)::btnr -> (tm2,n2)::insertnewdelayed (tm,n) btnr

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
        bestnode := n2;
	netblkh := node_blockheight !bestnode;
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
	blockheader_succ_a tmstamp currtinfo blkh1
      then
	begin
	  if not (DbBlockHeader.dbexists h) then DbBlockHeader.dbput h blkh1;
          Hashtbl.add blkheaders h ();
	  broadcast_inv [(int_of_msgtype Headers,blkhght,h)];
          let (csm1,fsm1,tar1) = currtinfo in
          let newcumulstake = cumul_stake prevcumulstk tar1 blkhd1.deltatime in
	  let validated = ref (if knownvalid then ValidBlock else Waiting(Unix.time())) in
          let newnode = BlocktreeNode(Some(prevnode),ref [blkhd1.stakeaddr],Some(h),blkhd1.newtheoryroot,blkhd1.newsignaroot,blkhd1.newledgerroot,blkhd1.tinfo,blkhd1.timestamp,newcumulstake,Int64.add blkhght 1L,validated,ref false,ref []) in
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
		      broadcast_requestdata GetSTx txh
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
		      validated := ValidBlock;
		      if not initialization then add_to_validheaders_file hh;
                      let BlocktreeNode(_,_,_,_,_,_,_,_,bestcumulstk,_,_,_,_) = !bestnode in
		      if gt_big_int newcumulstake bestcumulstk then
			begin
			  bestnode := newnode;
			  netblkh := node_blockheight !bestnode
			end;
		      add_thytree blkhd1.newtheoryroot !latesttht;
		      add_sigtree blkhd1.newsignaroot !latestsigt;
		      broadcast_inv [(int_of_msgtype Blockdelta,blkhght,h)];
		      (*** construct a transformed tree consisting of elements ***)
		      let prevc = load_expanded_ctree (ctree_of_block blk) in
		      match txl_octree_trans blkhght (txl_of_block blk) (Some(prevc)) with
		      | Some(newc) -> ignore (save_ctree_elements newc)
                      | None -> raise (Failure("transformed tree was empty, although block seemed to be valid"))
		    end
		  else
		    begin
		      validated := InvalidBlock; (*** could delete and possibly blacklist the qblockdeltah, but will leave it for now ***)
		    end
	    with
	    | Not_found -> (*** request blockdeltah h from peers ***)
		broadcast_requestdata GetBlockdeltah h
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
                bestnode := newnode;
		netblkh := node_blockheight !bestnode
	      end;
            List.iter
              (fun (h,blkh1) -> let (blkhd1,_) = blkh1 in process_new_header_a h (hashval_hexstring h) blkh1 blkhd1 initialization knownvalid)
              (Hashtbl.find_all orphanblkheaders (Some(h)))
        end
      else
        begin (*** if it's wrong, delete it and blacklist it so it won't look new in the future ***)
          DbBlacklist.dbput h true;
	  DbBlockHeader.dbdelete h;
        end
    with Not_found -> (*** orphan block header, put it on the relevant hash table and request parent ***)
      Hashtbl.add orphanblkheaders prevblkh (h,blkh1);
      match prevblkh with
      | Some(pbh) ->
	  if DbBlockHeader.dbexists pbh then
	    process_new_header pbh (hashval_hexstring pbh) initialization knownvalid
	  else
	    broadcast_requestdata GetHeader pbh
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
	  Printf.printf "processing valid header %s\n" h; flush stdout;
          process_new_header (hexstring_hashval h) h true knownvalid
        done
      with End_of_file -> close_in f
    end
  else
    ()

let init_headers () =
  init_headers_a (Filename.concat (datadir()) "validheaders") true;
  init_headers_a (Filename.concat (datadir()) "headers") false

let initblocktree () =
  genesisblocktreenode := BlocktreeNode(None,ref [],None,None,None,!genesisledgerroot,(!genesiscurrentstakemod,!genesisfuturestakemod,!genesistarget),!Config.genesistimestamp,zero_big_int,1L,ref ValidBlock,ref false,ref []);
  lastcheckpointnode := !genesisblocktreenode;
  bestnode := !genesisblocktreenode;
  netblkh := node_blockheight !bestnode;
  Hashtbl.add blkheadernode None !genesisblocktreenode;
  init_headers()

let rec find_best_validated_block_from fromnode bestcumulstk =
  let BlocktreeNode(_,_,_,_,_,_,_,_,cumulstk,_,validatedp,blklistp,succl) = fromnode in
  if not !blklistp && !validatedp = ValidBlock then
    begin
      let newbestcumulstk = ref
	(if gt_big_int cumulstk bestcumulstk then
	  begin
	    bestnode := fromnode;
	    netblkh := node_blockheight !bestnode;
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
  if not (Hashtbl.mem stxpool txh) then Hashtbl.add stxpool txh stx1;
  DbTx.dbput txh tx1;
  DbTxSignatures.dbput txh txsigs1;
  Hashtbl.add published_stx txh ();
  broadcast_inv [(int_of_msgtype STx,0L,txh)]

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
  ();;

Hashtbl.add msgtype_handler NewHeader
  (fun (sin,sout,cs,ms) ->
    let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
    if not (DbBlockHeader.dbexists h) then
      let i = int_of_msgtype GetHeader in
      cs.invreq <- (i,h)::cs.invreq;
      ignore (queue_msg cs GetHeader ms));;

Hashtbl.add msgtype_handler GetHeader
  (fun (sin,sout,cs,ms) ->
    let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
    let i = int_of_msgtype GetHeader in
    if not (List.mem (i,h) cs.sentinv) then (*** don't resend ***)
      try
	let bh = DbBlockHeader.dbget h in
	let s = Buffer.create 1000 in
	seosbf (seo_blockheader seosb bh (seo_hashval seosb h (seo_int8 seosb 1 (s,None))));
	cs.sentinv <- (i,h)::cs.sentinv;
	ignore (queue_msg cs Headers (Buffer.contents s))
      with Not_found ->
	(*** don't have it to send, ignore ***)
	());;

Hashtbl.add msgtype_handler GetHeaders
  (fun (sin,sout,cs,ms) ->
    let c = ref (ms,String.length ms,None,0,0) in
    let m = ref 0 in
    let bhl = ref [] in
    let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
    c := cn;
    let i = int_of_msgtype GetHeader in
    for j = 1 to n do
      let (h,cn) = sei_hashval seis !c in
      c := cn;
      if not (List.mem (i,h) cs.sentinv) then (*** don't resend ***)
	try
	  let bh = DbBlockHeader.dbget h in
	  incr m;
	  bhl := (h,bh)::!bhl;
	  cs.sentinv <- (i,h)::cs.sentinv
	with Not_found ->
	  (*** don't have it to send, ignore ***)
	    ()
      done;
    let s = Buffer.create 10000 in
    let co = ref (seo_int8 seosb !m (s,None)) in
    List.iter (fun (h,bh) -> co := seo_blockheader seosb bh (seo_hashval seosb h !co)) !bhl;
    seosbf !co;
    ignore (queue_msg cs Headers (Buffer.contents s))
  );;

Hashtbl.add msgtype_handler Headers
  (fun (sin,sout,cs,ms) ->
    let c = ref (ms,String.length ms,None,0,0) in
    let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
    c := cn;
    let i = int_of_msgtype GetHeader in
    for j = 1 to n do
      let (h,cn) = sei_hashval seis !c in
      let (bh,cn) = sei_blockheader seis cn in (*** deserialize if only to get to the next one ***)
      c := cn;
      if not (DbBlockHeader.dbexists h) && List.mem (i,h) cs.invreq then
	let (bhd,bhs) = bh in
	if hash_blockheaderdata bhd = h then
	  process_new_header_a h (hashval_hexstring h) bh bhd false false
	else
	  begin
	    Printf.fprintf !log "got a header with the wrong hash, dropping it\n"; flush !log;
	  end
    done);;

let req_headers sout cs m nw =
  if m > 0 then
    begin
      let s = Buffer.create 1000 in
      let co = ref (seo_int8 seosb m (s,None)) in
      List.iter (fun h -> co := seo_hashval seosb h !co) nw;
      seosbf !co;
      ignore (queue_msg cs GetHeaders (Buffer.contents s))
    end;;

let rec req_header_batches sout cs m hl nw =
  if m = 255 then
    (req_headers sout cs m nw; req_header_batches sout cs 0 hl [])
  else
    match hl with
    | (_,h)::hr ->
	let i = int_of_msgtype GetHeader in
	cs.invreq <- (i,h)::cs.invreq;
	req_header_batches sout cs (m+1) hr (h::nw)
    | [] -> req_headers sout cs m nw;;

Hashtbl.add msgtype_handler Inv
  (fun (sin,sout,cs,ms) ->
    let c = ref (ms,String.length ms,None,0,0) in
    let hl = ref [] in
    let (n,cn) = sei_int32 seis !c in
    Printf.fprintf !log "Inv %ld\n" n;
    c := cn;
    for j = 1 to Int32.to_int n do
      let ((i,blkh,h),cn) = sei_prod3 sei_int8 sei_int64 sei_hashval seis !c in
      Printf.fprintf !log "%d %Ld %s\n" i blkh (hashval_hexstring h);
      c := cn;
      cs.rinv <- (i,h)::cs.rinv;
      if i = int_of_msgtype Headers && not (DbBlockHeader.dbexists h) && not (DbArchived.dbexists h) then
	hl := List.merge (fun (blkh1,_) (blkh2,_) -> compare blkh2 blkh1) !hl [(blkh,h)] (*** reverse order because they will be reversed again when requested ***)
      else if i = int_of_msgtype STx && not (DbArchived.dbexists h) then
	begin
	  if DbTx.dbexists h then
	    if not (DbTxSignatures.dbexists h) then
	      begin
                cs.invreq <- (int_of_msgtype GetTxSignatures,h)::cs.invreq;
		let s = Buffer.create 1000 in
		seosbf (seo_hashval seosb h (s,None));
		ignore (queue_msg cs GetTxSignatures (Buffer.contents s))
	      end
            else ()
          else
 	    begin
              cs.invreq <- (int_of_msgtype GetTx,h)::cs.invreq;
              let s = Buffer.create 1000 in
	      seosbf (seo_hashval seosb h (s,None));
	      ignore (queue_msg cs GetTx (Buffer.contents s))
	    end
	end
    done;
    req_header_batches sout cs 0 !hl []);;

Hashtbl.add msgtype_handler GetTx
    (fun (sin,sout,cs,ms) ->
      Printf.fprintf !log "Processing GetTx\n";
      let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
      Printf.fprintf !log "Processing GetTx %s\n" (hashval_hexstring h);
      let i = int_of_msgtype GetTx in
      if not (List.mem (i,h) cs.sentinv) then (*** don't resend ***)
	try
	  let (tau,_) = Hashtbl.find stxpool h in
	  let tausb = Buffer.create 100 in
	  seosbf (seo_tx seosb tau (seo_hashval seosb h (tausb,None)));
	  let tauser = Buffer.contents tausb in
	  Printf.fprintf !log "Sending Tx (from pool) %s\n" (hashval_hexstring h);
	  ignore (queue_msg cs Tx tauser);
	  cs.sentinv <- (i,h)::cs.sentinv
	with Not_found ->
	  try
	    let tau = DbTx.dbget h in
	    let tausb = Buffer.create 100 in
	    seosbf (seo_tx seosb tau (seo_hashval seosb h (tausb,None)));
	    let tauser = Buffer.contents tausb in
	    Printf.fprintf !log "Sending Tx (from db) %s\n" (hashval_hexstring h);
	    ignore (queue_msg cs Tx tauser);
	    cs.sentinv <- (i,h)::cs.sentinv
	  with Not_found ->
	    Printf.fprintf !log "Unknown Tx %s\n" (hashval_hexstring h);
	    ());;

Hashtbl.add msgtype_handler Tx
    (fun (sin,sout,cs,ms) ->
      let (h,r) = sei_hashval seis (ms,String.length ms,None,0,0) in
      let i = int_of_msgtype GetTx in
      if not (DbTx.dbexists h) then (*** if we already have it, abort ***)
	if List.mem (i,h) cs.invreq then (*** only continue if it was requested ***)
          let (tau,_) = sei_tx seis r in
	  if hashtx tau = h then
	    begin
  	      DbTx.dbput h tau;
	      cs.invreq <- List.filter (fun (j,k) -> not (i = j && h = k)) cs.invreq
	    end
          else (*** otherwise, it seems to be a misbehaving peer --  ignore for now ***)
	    (Printf.fprintf !Utils.log "misbehaving peer? [malformed Tx]\n"; flush !Utils.log)
	else (*** if something unrequested was sent, then seems to be a misbehaving peer ***)
	  (Printf.fprintf !Utils.log "misbehaving peer? [unrequested Tx]\n"; flush !Utils.log));;

Hashtbl.add msgtype_handler GetTxSignatures
    (fun (sin,sout,cs,ms) ->
      let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
      Printf.fprintf !log "Processing GetTxSignatures %s\n" (hashval_hexstring h);
      let i = int_of_msgtype GetTxSignatures in
      if not (List.mem (i,h) cs.sentinv) then (*** don't resend ***)
	try
	  let (_,s) = Hashtbl.find stxpool h in
	  let ssb = Buffer.create 100 in
	  seosbf (seo_txsigs seosb s (seo_hashval seosb h (ssb,None)));
	  let sser = Buffer.contents ssb in
	  Printf.fprintf !log "Sending TxSignatures (from pool) %s\n" (hashval_hexstring h);
	  ignore (queue_msg cs TxSignatures sser);
	  cs.sentinv <- (i,h)::cs.sentinv
	with Not_found ->
	  try
	    let s = DbTxSignatures.dbget h in
	    let ssb = Buffer.create 100 in
	    seosbf (seo_txsigs seosb s (seo_hashval seosb h (ssb,None)));
	    let sser = Buffer.contents ssb in
	    Printf.fprintf !log "Sending TxSignatures (from db) %s\n" (hashval_hexstring h);
	    ignore (queue_msg cs TxSignatures sser);
	    cs.sentinv <- (i,h)::cs.sentinv
	with Not_found ->
	  Printf.fprintf !log "Unknown TxSignatures %s\n" (hashval_hexstring h);
	  ());;

Hashtbl.add msgtype_handler TxSignatures
    (fun (sin,sout,cs,ms) ->
      let (h,r) = sei_hashval seis (ms,String.length ms,None,0,0) in
      let i = int_of_msgtype GetTxSignatures in
      if not (DbTxSignatures.dbexists h) then (*** if we already have it, abort ***)
	try
	  let ((tauin,_) as tau) = DbTx.dbget h in
	  if List.mem (i,h) cs.invreq then (*** only continue if it was requested ***)
            let (s,_) = sei_txsigs seis r in
	    try
	      let al = List.map (fun (_,aid) -> DbAsset.dbget aid) tauin in
	      ignore (tx_signatures_valid_asof_blkh al (tau,s)); (*** signatures valid at some block height ***)
              Hashtbl.add stxpool h (tau,s);
  	      DbTxSignatures.dbput h s;
	      cs.invreq <- List.filter (fun (j,k) -> not (i = j && h = k)) cs.invreq
	    with
	    | BadOrMissingSignature -> (*** otherwise, it seems to be a misbehaving peer --  ignore for now ***)
		(Printf.fprintf !Utils.log "misbehaving peer? [malformed TxSignatures]\n"; flush !Utils.log)
	    | Not_found -> (*** in this case, we don't have all the spent assets in the database, which means we shouldn't have requested the signatures, ignore ***)
		()
	  else (*** if something unrequested was sent, then seems to be a misbehaving peer ***)
	    (Printf.fprintf !Utils.log "misbehaving peer? [unrequested TxSignatures]\n"; flush !Utils.log)
	with Not_found -> (*** do not know the tx, so drop the sig ***)
	  ());;

