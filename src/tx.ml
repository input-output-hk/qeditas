(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Ser
open Sha256
open Hash
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
  | (alpha,(_,TheoryPublication(beta,h,dl)))::outpr -> pubaddr_p alpha && tx_outputs_valid_addr_cats outpr
  | (alpha,(_,SignaPublication(beta,h,th,dl)))::outpr -> pubaddr_p alpha && tx_outputs_valid_addr_cats outpr
  | (alpha,(_,DocPublication(beta,h,th,dl)))::outpr -> pubaddr_p alpha && tx_outputs_valid_addr_cats outpr
  | _::outpr -> tx_outputs_valid_addr_cats outpr
  | [] -> true

let tx_outputs_valid (outpl: addr_preasset list) =
  tx_outputs_valid_one_owner outpl [] [] []
    &&
  tx_outputs_valid_addr_cats outpl 

let tx_valid tau = tx_inputs_valid (tx_inputs tau) && tx_outputs_valid (tx_outputs tau)

type stx = tx * (gensignat list * gensignat list)

let check_spend_obligation alpha blkh (txhe:big_int) s obl =
  match obl with
  | None -> (*** defaults to alpha with no block height restriction ***)
      verify_gensignat txhe s alpha
  | Some(gamma,b,_) ->
      b <= blkh && verify_gensignat txhe s (Hash.payaddr_addr gamma)

let check_move_obligation alpha txhe s obl2 u2 outpl =
  try
    if not (payaddr_p alpha) then raise Not_found; (*** things held and termaddrs and pubaddrs should not be "moved" in this way ***)
    ignore (List.find (fun z -> let (beta,(obl,u)) = z in obl = obl2 && u = u2) outpl);
    verify_gensignat txhe s alpha
  with Not_found -> false

let rec check_tx_in_signatures blkh txhe outpl inpl al sl =
  match inpl,al with
  | [],[] -> true
  | (alpha,k)::inpr,(a::ar) ->
      check_tx_in_signatures blkh txhe outpl inpr ar sl
	&&
      assetid a = k
	&&
      begin
	try
	  ignore (List.find
		    (fun s ->
		      check_spend_obligation alpha blkh txhe s (assetobl a) || check_move_obligation alpha txhe s (assetobl a) (assetpre a) outpl)
		    sl);
	  true
	with Not_found -> false
      end
  | _,_ -> false

let rec check_tx_out_signatures blkh txhe outpl sl =
  match outpl,sl with
  | [],[] -> true
  | (_,(_,TheoryPublication(alpha,n,thy)))::outpr,sg::sr ->
      check_tx_out_signatures blkh txhe outpr sr
	&&
      verify_gensignat txhe sg (payaddr_addr alpha)
  | (_,(_,SignaPublication(alpha,n,th,si)))::outpr,sg::sr ->
      check_tx_out_signatures blkh txhe outpr sr
	&&
      verify_gensignat txhe sg (payaddr_addr alpha)
  | (_,(_,DocPublication(alpha,n,th,d)))::outpr,sg::sr ->
      check_tx_out_signatures blkh txhe outpr sr
	&&
      verify_gensignat txhe sg (payaddr_addr alpha)
  | _::outpr,_ -> check_tx_out_signatures blkh txhe outpr sl
  | _,_ -> false

let tx_signatures_valid blkh al stau =
  let (tau,(sli,slo)) = stau in
  let txhe = hashval_big_int (hashtx tau) in
  check_tx_in_signatures blkh txhe (tx_outputs tau) (tx_inputs tau) al sli
    &&
  check_tx_out_signatures blkh txhe (tx_outputs tau) slo

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
      let sgh = hashsigna sg in
      txout_update_ostree outpr (Some(ostree_insert sigt (hashval_bitseq sgh) th sg))
  | _::outpr -> txout_update_ostree outpr sigt

let tx_update_ostree tau sigt = txout_update_ostree (tx_outputs tau) sigt
