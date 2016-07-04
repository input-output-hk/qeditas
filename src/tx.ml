(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Ser
open Sha256
open Hash
open Net
open Db
open Mathdata
open Assets
open Secp256k1
open Cryptocurr
open Signat
open Script

type tx = addr_assetid list * addr_preasset list

let hashtx (inpl,outpl) =
  hashpair
    (hashlist (List.map hash_addr_assetid inpl))
    (hashlist (List.map hash_addr_preasset outpl))

let tx_inputs ((inpl,outpl):tx) = inpl
let tx_outputs ((inpl,outpl):tx) = outpl

let rec no_dups l =
  match l with
  | [] -> true
  | x::r when List.mem x r -> false
  | _::r -> no_dups r

let tx_inputs_valid inpl =
  match inpl with
  | [] -> false
  | _ -> no_dups inpl

(*** Ensure at most one owner is declared for each object/proposition ***)
let rec tx_outputs_valid_one_owner outpl ool pol nol =
  match outpl with
  | (alpha,(_,OwnsObj(beta,io)))::outpr ->
      if List.mem alpha ool then
	false
      else
	tx_outputs_valid_one_owner outpr (alpha::ool) pol nol
  | (alpha,(_,OwnsProp(beta,io)))::outpr ->
      if List.mem alpha pol then
	false
      else
	tx_outputs_valid_one_owner outpr ool (alpha::pol) nol
  | (alpha,(_,OwnsNegProp))::outpr ->
      if List.mem alpha nol then
	false
      else
	tx_outputs_valid_one_owner outpr ool pol (alpha::nol)
  | _::outpr -> tx_outputs_valid_one_owner outpr ool pol nol
  | [] -> true

(*** Ensure ownership deeds are sent to term addresses and publications are sent to publication addresses. ***)
let rec tx_outputs_valid_addr_cats outpl =
  match outpl with
  | (alpha,(_,OwnsObj(beta,u)))::outpr -> termaddr_p alpha && tx_outputs_valid_addr_cats outpr
  | (alpha,(_,OwnsProp(beta,u)))::outpr -> termaddr_p alpha && tx_outputs_valid_addr_cats outpr
  | (alpha,(_,OwnsNegProp))::outpr -> termaddr_p alpha && tx_outputs_valid_addr_cats outpr
  | (alpha,(_,TheoryPublication(beta,h,dl)))::outpr ->
      begin
	match hashtheory (theoryspec_theory dl) with
	| Some(dlh) ->
	    alpha = hashval_pub_addr dlh && tx_outputs_valid_addr_cats outpr
	| None -> false
      end
  | (alpha,(_,SignaPublication(beta,h,th,dl)))::outpr ->
      alpha = hashval_pub_addr (hashopair2 th (hashsigna (signaspec_signa dl))) && tx_outputs_valid_addr_cats outpr
  | (alpha,(_,DocPublication(beta,h,th,dl)))::outpr -> alpha = hashval_pub_addr (hashopair2 th (hashdoc dl)) && tx_outputs_valid_addr_cats outpr
  | (alpha,(_,Marker))::outpr -> pubaddr_p alpha && tx_outputs_valid_addr_cats outpr (*** markers should only be published to publication addresses, since they're used to prepublish an intention to publish ***)
  | _::outpr -> tx_outputs_valid_addr_cats outpr
  | [] -> true

let tx_outputs_valid (outpl: addr_preasset list) =
  tx_outputs_valid_one_owner outpl [] [] []
    &&
  tx_outputs_valid_addr_cats outpl 

let tx_valid tau = tx_inputs_valid (tx_inputs tau) && tx_outputs_valid (tx_outputs tau)

type stx = tx * (gensignat list * gensignat list)

exception BadOrMissingSignature

let opmax b1 b2 =
  match (b1,b2) with
  | (Some(b1),Some(b2)) -> if b1 > b2 then Some(b1) else Some(b2)
  | (_,None) -> b1
  | _ -> b2

let check_spend_obligation_upto_blkh alpha (txhe:big_int) s obl =
  match obl with
  | None -> (*** defaults to alpha with no block height restriction ***)
      if verify_gensignat txhe s alpha then
	None
      else
	raise BadOrMissingSignature
  | Some(gamma,b,_) ->
      if verify_gensignat txhe s (Hash.payaddr_addr gamma) then
	Some(b)
      else
	raise BadOrMissingSignature

let check_spend_obligation alpha blkh (txhe:big_int) s obl =
  try
    match check_spend_obligation_upto_blkh alpha txhe s obl with
    | None -> true
    | Some(b) -> b <= blkh
  with BadOrMissingSignature -> false

let check_move_obligation alpha txhe s obl2 u2 outpl =
  try
    if not (payaddr_p alpha) then raise Not_found; (*** things held and termaddrs and pubaddrs should not be "moved" in this way ***)
    ignore (List.find (fun z -> let (beta,(obl,u)) = z in obl = obl2 && u = u2) outpl);
    verify_gensignat txhe s alpha
  with Not_found -> false

let rec check_tx_in_signatures txhe outpl inpl al sl =
  match inpl,al with
  | [],[] -> None
  | (alpha,k)::inpr,(a::ar) ->
      let b = ref (check_tx_in_signatures txhe outpl inpr ar sl) in
      if assetid a = k then
	begin
	  match assetpre a with
	  | Marker -> !b
	  | Bounty(_) -> !b
	  | _ -> (*** don't require signatures to spend markers and bounties; but there are conditions for the tx to be supported by a ctree ***)
	      try
		ignore (List.find
			  (fun s ->
			    try
			      let b2 = check_spend_obligation_upto_blkh alpha txhe s (assetobl a) in
			      b := opmax !b b2;
			      true
			    with BadOrMissingSignature ->
			      if check_move_obligation alpha txhe s (assetobl a) (assetpre a) outpl then
				true
			      else
				false)
			  sl);
		!b
	      with Not_found ->
		raise BadOrMissingSignature
	end
      else
	raise BadOrMissingSignature
  | _,_ ->
      raise BadOrMissingSignature

let rec check_tx_out_signatures txhe outpl sl =
  match outpl with
  | [] -> true
  | (_,(_,TheoryPublication(alpha,n,thy)))::outpr ->
      check_tx_out_signatures txhe outpr sl
	&&
      (try ignore (List.find (fun sg -> verify_gensignat txhe sg (payaddr_addr alpha)) sl); true with Not_found -> false)
  | (_,(_,SignaPublication(alpha,n,th,si)))::outpr ->
      check_tx_out_signatures txhe outpr sl
	&&
      (try ignore (List.find (fun sg -> verify_gensignat txhe sg (payaddr_addr alpha)) sl); true with Not_found -> false)
  | (_,(_,DocPublication(alpha,n,th,d)))::outpr ->
      check_tx_out_signatures txhe outpr sl
	&&
      (try ignore (List.find (fun sg -> verify_gensignat txhe sg (payaddr_addr alpha)) sl); true with Not_found -> false)
  | _::outpr ->
      check_tx_out_signatures txhe outpr sl

let tx_signatures_valid_asof_blkh al stau =
  let (tau,(sli,slo)) = stau in
  let txh = if !Config.testnet then hashtag (hashtx tau) 288l else hashtx tau in (*** sign a modified hash for testnet ***)
  let txhe = hashval_big_int txh in
  let b = check_tx_in_signatures txhe (tx_outputs tau) (tx_inputs tau) al sli in
  if check_tx_out_signatures txhe (tx_outputs tau) slo then
    b
  else
    raise BadOrMissingSignature

let tx_signatures_valid blkh al stau =
  try
    match tx_signatures_valid_asof_blkh al stau with
    | Some(b) -> b <= blkh
    | None -> true
  with BadOrMissingSignature -> false

let rec txout_update_ottree outpl tht =
  match outpl with
  | [] -> tht
  | (alpha,(obl,TheoryPublication(gamma,nonce,d)))::outpr ->
      let thy = theoryspec_theory d in
      begin
	match hashtheory thy with
	| Some(thyh) ->
	    txout_update_ottree outpr (Some(ottree_insert tht (hashval_bitseq thyh) thy))
	| _ -> txout_update_ottree outpr tht
      end
  | _::outpr -> txout_update_ottree outpr tht

let tx_update_ottree tau tht = txout_update_ottree (tx_outputs tau) tht

let rec txout_update_ostree outpl sigt =
  match outpl with
  | [] -> sigt
  | (alpha,(obl,SignaPublication(gamma,nonce,th,d)))::outpr ->
      let sg = signaspec_signa d in
      let thsgh = hashopair2 th (hashsigna sg) in
      txout_update_ostree outpr (Some(ostree_insert sigt (hashval_bitseq thsgh) sg))
  | _::outpr -> txout_update_ostree outpr sigt

let tx_update_ostree tau sigt = txout_update_ostree (tx_outputs tau) sigt

let seo_tx o g c = seo_prod (seo_list seo_addr_assetid) (seo_list seo_addr_preasset) o g c
let sei_tx i c = sei_prod (sei_list sei_addr_assetid) (sei_list sei_addr_preasset) i c
let seo_txsigs o g c = seo_prod (seo_list seo_gensignat) (seo_list seo_gensignat) o g c
let sei_txsigs i c = sei_prod (sei_list sei_gensignat) (sei_list sei_gensignat) i c
let seo_stx o g c = seo_prod seo_tx seo_txsigs o g c
let sei_stx i c = sei_prod sei_tx sei_txsigs i c

module DbTx = Dbbasic (struct type t = tx let basedir = "tx" let seival = sei_tx seic let seoval = seo_tx seoc end)

module DbTxSignatures = Dbbasic (struct type t = gensignat list * gensignat list let basedir = "txsigs" let seival = sei_txsigs seic let seoval = seo_txsigs seoc end);;

Hashtbl.add msgtype_handler GetTx
    (fun (sin,sout,cs,ms) ->
      let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
      let i = int_of_msgtype GetTx in
      if not (List.mem (i,h) cs.sentinv) then (*** don't resend ***)
	try
	  let tau = DbTx.dbget h in
	  let tausb = Buffer.create 100 in
	  seosbf (seo_tx seosb tau (tausb,None));
	  let tauser = Buffer.contents tausb in
	  ignore (send_msg sout Tx tauser);
	  cs.sentinv <- (i,h)::cs.sentinv
	with Not_found -> ());;

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
      let i = int_of_msgtype GetTxSignatures in
      if not (List.mem (i,h) cs.sentinv) then (*** don't resend ***)
	try
	  let s = DbTxSignatures.dbget h in
	  let ssb = Buffer.create 100 in
	  seosbf (seo_txsigs seosb s (ssb,None));
	  let sser = Buffer.contents ssb in
	  ignore (send_msg sout TxSignatures sser);
	  cs.sentinv <- (i,h)::cs.sentinv
	with Not_found -> ());;

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

