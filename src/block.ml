(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Mathdata
open Assets
open Signat
open Tx
open Ctre
open Ctregraft

let maturation_post_staking = 144L
let maturation_pre_staking = 36L
let not_close_to_mature = 144L

(*** base reward of 50 fraenks (50 trillion cants) like bitcoin, but assume the first 350000 blocks have passed. ***)
let basereward = 50000000000000000L

let rewfn blkh =
  if blkh < 11410000L then
    let blki = Int64.to_int blkh in
    Int64.shift_right basereward ((blki + 350000) / 210000)
  else
    0L

type targetinfo = unit (* to do *)

let hashtargetinfo ti = hashint64 256L (* to do *)

type por =
  | PorTrm of termaddr * hashval * tm
  | PorDoc of pubaddr * hashval * pdoc

let hashpor r =
  match r with
  | PorTrm(k,h,m) -> hashtag (hashpair k (hashpair h (hashtm m))) 192l
  | PorDoc(k,h,d) -> hashtag (hashpair k (hashpair h (hashpdoc d))) 193l

let hashopor r =
  match r with
  | Some(r) -> Some(hashpor r)
  | None -> None

type blockheader = {
    prevblockhash : hashval option;
    newtheoryroot : hashval option;
    newsignaroot : hashval option;
    newledgerroot : hashval;
    stake : int64;
    stakeaddr : p2pkhaddr;
    stakeassetid : hashval;
    retrievable : por option;
    timestamp : int64;
    tinfo : targetinfo;
    prevledger : ctree;
    blocksignat : signat;
    blocksignatrecid : int;
    blocksignatfcomp : bool;
  }

type blockdelta = {
    stakeoutput : addr_preasset list;
    totalfees : int64;
    prevledgergraft : cgraft;
    blockdelta_stxl : stx list
  }

type block = blockheader * blockdelta

let check_hit blkh bh = true (* to do *)

let coinstake b =
  let (bh,bd) = b in
  ([(p2pkhaddr_addr bh.stakeaddr,bh.stakeassetid)],bd.stakeoutput)

let hash_blockheader bh =
  hashopair2 bh.prevblockhash
    (hashpair
       (hashopair2 bh.newtheoryroot
	  (hashopair2 bh.newsignaroot
	     bh.newledgerroot))
       (hashpair
	  (hashpair (hashint64 bh.stake) (hashpair bh.stakeaddr bh.stakeassetid))
	  (hashopair2
	     (hashopor bh.retrievable)
	     (hashpair
		(hashtargetinfo bh.tinfo)
		(hashpair (hashint64 bh.timestamp) (ctree_hashroot bh.prevledger))))))

let valid_blockheader blkh bh =
  verify_p2pkhaddr_signat (hashval_big_int (hash_blockheader bh)) bh.stakeaddr bh.blocksignat bh.blocksignatrecid bh.blocksignatfcomp
    &&
  check_hit blkh bh
    &&
  begin
    match ctree_lookup_asset bh.stakeassetid bh.prevledger (addr_bitseq (p2pkhaddr_addr bh.stakeaddr)) with
    | Some(aid,bday,None,Currency(v)) when v = bh.stake -> (*** stake belongs to staker ***)
	Int64.add bday maturation_pre_staking <= blkh || bday = 0L
    | Some(aid,bday,Some(beta,n),Currency(v)) when v = bh.stake -> (*** stake is on loan for staking ***)
	Int64.add bday maturation_pre_staking <= blkh
	  &&
	n > Int64.add blkh not_close_to_mature
    | _ -> false
  end



let ctree_of_block b =
  let (bh,bd) = b in
  ctree_cgraft bd.prevledgergraft bh.prevledger

let rec stxs_allinputs stxl =
  match stxl with
  | ((inpl,_),_)::stxr -> inpl @ stxs_allinputs stxr
  | [] -> []

let rec stxs_alloutputs stxl =
  match stxl with
  | ((_,outpl),_)::stxr -> outpl @ stxs_alloutputs stxr
  | [] -> []

let tx_of_block b =
  let (bh,bd) = b in
  ((p2pkhaddr_addr bh.stakeaddr,bh.stakeassetid)::stxs_allinputs bd.blockdelta_stxl,bd.stakeoutput @ stxs_alloutputs bd.blockdelta_stxl)

let valid_block tht sigt blkh b =
  let (bh,bd) = b in
  (*** The header is valid. ***)
  valid_blockheader blkh bh
    &&
  tx_outputs_valid bd.stakeoutput
    &&
  List.fold_left
    (fun b (alpha,(obl,u)) ->
      b &&
      match obl with
      | Some(a,n) -> n > Int64.add blkh maturation_post_staking
      | None -> false
    )
    true
    bd.stakeoutput
    &&
  let tr = ctree_of_block b in (*** let tr be the ctree of the block, used often below ***)
  begin
    try
      let z = ctree_supports_tx tht sigt blkh (coinstake b) tr in
      z = Int64.add (rewfn blkh) bd.totalfees
    with NotSupported -> false
  end
    &&
  (*** There are no duplicate transactions. ***)
  no_dups bd.blockdelta_stxl
    &&
  (*** The cgraft is valid. ***)
  cgraft_valid bd.prevledgergraft
    &&
  let stakealpha1 = p2pkhaddr_addr bh.stakeaddr in
  let stakein = (stakealpha1,bh.stakeassetid) in
  (*** Each transaction in the delta has supported elaborated assets and is appropriately signed. ***)
  (*** Also, each transaction in the delta is valid and supported without a reward. ***)
  (*** Also, no transaction has the stake asset as an input. ***)
  begin
    try
      List.fold_left
	(fun sgvb stau ->
	  match stau with
	  | ((inpl,_) as tau,_) ->
	      let aal = ctree_lookup_input_assets inpl tr in
	      let al = List.map (fun (_,a) -> a) aal in
	      sgvb
		&& not (List.mem stakein inpl)
		&& tx_signatures_valid blkh al stau
		&& tx_valid tau
		&& ctree_supports_tx_2 tht sigt blkh tau aal al tr <= 0L
	)
	true
	bd.blockdelta_stxl
    with NotSupported -> false
  end
    &&
  (*** No distinct transactions try to spend the same asset. ***)
  (*** Also, wnership is not created for the same address alpha by two txs in the block. ***)
  begin
    try
      let stxlr = ref bd.blockdelta_stxl in
      while !stxlr != [] do
	match !stxlr with
	| ((inpl1,outpl1),_)::stxr ->
	    let hl1 = List.map (fun (_,h) -> h) inpl1 in
	    let oo1 = ref [] in
	    let op1 = ref [] in
	    List.iter
	      (fun (alpha1,(obl1,u1)) ->
		match u1 with
		| OwnsObj(_,_) -> oo1 := alpha1::!oo1
		| OwnsProp(_,_) -> op1 := alpha1::!op1
		| _ -> ())
	      outpl1;
	    stxlr := stxr;
	    List.iter
	      (fun ((inpl2,outpl2),_) ->
		List.iter
		  (fun (_,h) ->
		    if List.mem h hl1 then
		      raise NotSupported (*** This is a minor abuse of this exception. There could be a separate exception for this case. ***)
		  ) inpl2;
		List.iter
		  (fun (alpha2,(obl2,u2)) ->
		    match u2 with
		    | OwnsObj(_,_) ->
			if List.mem alpha2 !oo1 then raise NotSupported
		    | OwnsProp(_,_) ->
			if List.mem alpha2 !op1 then raise NotSupported
		    | _ -> ()
		  )
		  outpl2
	      )
	      stxr
	| [] -> ()
      done;
      true
    with NotSupported -> false
  end
    &&
  (*** Ownership is not created for the same address alpha by the coinstake and a tx in the block. ***)
  begin
    try
      List.iter
	(fun (alpha,(obl,u)) ->
	  match u with
	  | OwnsObj(_,_) ->
	      List.iter
		(fun ((_,outpl2),_) ->
		  List.iter
		    (fun (alpha2,(obl2,u2)) ->
		      if alpha = alpha2 then
			match u2 with
			| OwnsObj(_,_) -> raise NotSupported
			| _ -> ())
		    outpl2)
		bd.blockdelta_stxl
	  | OwnsProp(_,_) ->
	      List.iter
		(fun ((_,outpl2),_) ->
		  List.iter
		    (fun (alpha2,(obl2,u2)) ->
		      if alpha = alpha2 then
			match u2 with
			| OwnsProp(_,_) -> raise NotSupported
			| _ -> ())
		    outpl2)
		bd.blockdelta_stxl
	  | _ -> ()
	)
	bd.stakeoutput;
      true
    with NotSupported -> false
  end
    &&
  (*** The total inputs and outputs match up with the declared fee. ***)
  let tau = tx_of_block b in (*** let tau be the tx of the block ***)
  let (inpl,outpl) = tau in
  let aal = ctree_lookup_input_assets inpl tr in
  let al = List.map (fun (_,a) -> a) aal in
  Int64.add (out_cost outpl) bd.totalfees = Int64.add (asset_value_sum al) (rewfn blkh)
    &&
  (***
      The root of the transformed ctree is the newledgerroot in the header.
      Likewise for the transformed tht and sigt.
   ***)
  match tx_octree_trans blkh tau (Some(tr)) with
  | Some(tr2) ->
      bh.newledgerroot = ctree_hashroot tr2
	&&
      bh.newtheoryroot = ottree_hashroot (txout_update_ottree outpl tht)
	&&
      bh.newsignaroot = ostree_hashroot (txout_update_ostree outpl sigt)
  | None -> false

type blockchain = block * block list
type blockheaderchain = blockheader * blockheader list

let blockchain_headers bc =
  let ((bh,bd),bl) = bc in
  (bh,List.map (fun b -> let (bh,bd) = b in bh) bl)

let ledgerroot_of_blockchain bc =
  let ((bh,bd),bl) = bc in
  bh.newledgerroot

let rec valid_blockchain_aux blkh bl =
  match bl with
  | (b::br) ->
      if blkh > 0L then
	let (tht,sigt) = valid_blockchain_aux (Int64.sub blkh 1L) br in
	if valid_block tht sigt blkh b then
	  (txout_update_ottree (tx_outputs (tx_of_block b)) tht,
	   txout_update_ostree (tx_outputs (tx_of_block b)) sigt)
	else
	  raise NotSupported
      else
	raise NotSupported
  | [] ->
      if blkh = 0L then
	(None,None)
      else
	raise NotSupported

let valid_blockchain blkh bc =
  try
    let (b,bl) = bc in
    ignore (valid_blockchain_aux blkh (b::bl));
    true
  with NotSupported -> false

let rec valid_blockheaderchain_aux blkh bhl =
  match bhl with
  | (bh::bhr) ->
      if blkh > 0L then
	valid_blockheaderchain_aux (Int64.sub blkh 1L) bhr
	  && valid_blockheader blkh bh
      else
	false
  | [] -> blkh = 0L

let valid_blockheaderchain blkh bhc =
  match bhc with
  | (bh,bhr) -> valid_blockheaderchain_aux blkh (bh::bhr)
