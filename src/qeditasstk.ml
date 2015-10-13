(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* Code for the staking process, intended to be started and controlled by qeditasd *)

open Big_int;;
open Ser;;
open Hash;;
open Mathdata;;
open Assets;;
open Ctre;;
open Block;;
open Net;;

set_binary_mode_in stdin true;;
set_binary_mode_out stdout true;;

let staking = ref false;;
let stkassets = ref [];;
let strtrmassets = ref [];;
let strdocassets = ref [];;
let blkh = ref 0L;;
let sm = ref (0L,0L,0L,0L);;
let tar = ref zero_big_int;;

let main () =
  sethungsignalhandler();
  let stktm = ref (Int64.of_float (Unix.time ())) in
  while true do
    if !stktm > Int64.add (Int64.of_float (Unix.time ())) 3600L then Unix.sleep 300; (*** wait for five minutes and then catch up on precomputing stakes ***)
    match input_byte_nohang stdin 1.0 with
    | Some(z) when z = 66 -> (*** msg to start trying to stake on top of a different block ***)
	let (newblkh,_) = sei_int64 seic (stdin,None) in
	let (newtar,_) = sei_big_int_256 seic (stdin,None) in
	let (newsm,_) = sei_stakemod seic (stdin,None) in
	blkh := newblkh;
	tar := newtar;
	sm := newsm;
	stktm := Int64.of_float (Unix.time())
    | Some(z) when z = 83 -> (*** start staking ***)
	staking := true;
	stktm := Int64.of_float (Unix.time())
    | Some(z) when z = 80 -> (*** pause staking ***)
	staking := false
    | Some(z) when z = 82 -> (*** remove a staking or storage asset ***)
	let (dh,_) = sei_hashval seic (stdin,None) in
	stkassets := List.filter (fun (alpha,h,bday,obl,v,csta,csda) -> not (dh = h)) !stkassets;
	List.iter
	  (fun (alpha,h,bday,obl,v,csta,csda) ->
	    csta := List.filter (fun (th,m,a,h,betak) -> not (dh = h)) !csta;
	    csda := List.filter (fun (gamma,nonce,th,d,h,betak) -> not (dh = h)) !csda
	    )
	  !stkassets;
	strtrmassets := List.filter (fun (th,m,a,h,betak) -> not (dh = h)) !strtrmassets;
	strdocassets := List.filter (fun (gamma,nonce,th,d,h,betak) -> not (dh = h)) !strdocassets;
    | Some(z) when z = 114 -> (*** remove all staking and storage assets ***)
	stkassets := [];
	strtrmassets := [];
	strdocassets := [];
    | Some(z) when z = 67 -> (*** add a currency asset for staking ***)
	let (alpha,_) = sei_hashval seic (stdin,None) in
	let (h,_) = sei_hashval seic (stdin,None) in
	let (bday,_) = sei_int64 seic (stdin,None) in
	let (v,_) = sei_int64 seic (stdin,None) in
	let (obl,_) = sei_obligation seic (stdin,None) in
	let csta = ref (List.filter
			  (fun (th,m,a,h,betak) ->
			    let (_,_,_,_,x) = hashpair alpha betak in
			    Int32.logand x 0xffffl = 0l)
			  !strtrmassets)
	in
	let csda = ref (List.filter
			  (fun (gamma,nonce,th,d,h,betak) ->
			    let (_,_,_,_,x) = hashpair alpha betak in
			    Int32.logand x 0xffffl = 0l)
			  !strdocassets)
	in
	stkassets := (alpha,h,bday,obl,v,csta,csda)::!stkassets
    | Some(z) when z = 68 -> (*** add a doc asset for storage ***)
	let (h,_) = sei_hashval seic (stdin,None) in
	let (nonce,_) = sei_hashval seic (stdin,None) in
	let (gamma,_) = sei_payaddr seic (stdin,None) in
	let (th,_) = sei_option sei_hashval seic (stdin,None) in
	let (d,_) = sei_pdoc seic (stdin,None) in
	begin
	  try
	    let beta = hashpair (hashaddr (payaddr_addr gamma)) (hashpair nonce (hashopair2 th (pdoc_hashroot d))) in
	    let k = check_postor_pdoc_r d in
	    let betak = hashpair beta k in
	    strdocassets := (gamma,nonce,th,d,h,betak)::!strdocassets;
	    List.iter
	      (fun (alpha,h,bday,obl,v,csta,csda) ->
		let (_,_,_,_,x) = hashpair alpha betak in
		if Int32.logand x 0xffffl  = 0l then csda := (gamma,nonce,th,d,h,betak)::!csda)
	      !stkassets
	  with InappropriatePostor ->
	    ()
	end
    | Some(z) when z = 116 -> (*** set the earliest timestamp permitted for the successor block ***)
	let (tm,_) = sei_int64 seic (stdin,None) in
	stktm := tm
    | Some(z) when z = 84 -> (*** add a term asset for storage ***)
	let (h,_) = sei_hashval seic (stdin,None) in
	let (m,_) = sei_tm seic (stdin,None) in
	let (a,_) = sei_tp seic (stdin,None) in
	let (th,_) = sei_option sei_hashval seic (stdin,None) in
	begin
	  try
	    let beta = hashopair2 th (hashpair (tm_hashroot m) (hashtp a)) in
	    let k = check_postor_tm_r m in
	    let betak = hashpair beta k in
	    strtrmassets := (th,m,a,h,betak)::!strtrmassets;
	    List.iter
	      (fun (alpha,h,bday,obl,v,csta,csda) ->
		let (_,_,_,_,x) = hashpair alpha betak in
		if Int32.logand x 0xffffl  = 0l then csta := (th,m,a,h,betak)::!csta)
	      !stkassets
	  with InappropriatePostor ->
	    ()
	end
    | Some(_) -> (*** misunderstanding, output to stderr; parent should kill the staker and restart ***)
	output_char stderr 'E';
	flush stderr
    | None ->
	let futuretime = Int64.add (Int64.of_float (Unix.time ())) 3600L in
	if !staking then
	  while !stktm < futuretime do
	    List.iter
	      (fun (stkaddr,h,bday,obl,v,corrstrtrmassets,corrstrdocassets) ->
		if !staking then
		  let mtar = mult_big_int !tar (coinage !blkh bday obl (incrstake v)) in
		(*** first check if it would be a hit with some storage component: ***)
		  if lt_big_int (hitval !stktm h !sm) mtar then
		  begin (*** if so, then check if it's a hit without some storage component ***)
		    if lt_big_int (hitval !stktm h !sm) !tar then
		      begin
			staking := false;
			output_byte stdout 72; (*** Report Pure Stake Hit ***)
			let c = (stdout,None) in
			let c = seo_int64 seoc !stktm c in
			let c = seo_hashval seoc stkaddr c in
			let c = seo_hashval seoc h c in
			seocf c;
			flush stdout
		      end
		    else (*** if not, check if there is some storage that will make it a hit ***)
		      begin
			try
			  let (th,m,a,h,betak) =
			    List.find
			      (fun (th,m,a,h,betak) ->
				lt_big_int (hitval !stktm betak !sm) mtar)
			      !corrstrtrmassets
			  in
			  staking := false;
			  output_byte stdout 83; (*** Report Hit With Storage ***)
			  let c = (stdout,None) in
			  let c = seo_int64 seoc !stktm c in
			  let c = seo_hashval seoc stkaddr c in
			  let c = seo_hashval seoc h c in
			  let c = seo_postor seoc (PostorTrm(th,m,a,h)) c in
			  seocf c;
			  flush stdout
			with Not_found ->
			  try
			    let (gamma,nonce,th,d,h,betak) =
			      List.find
				(fun (gamma,nonce,th,d,h,betak) ->
				  lt_big_int (hitval !stktm betak !sm) mtar)
				!corrstrdocassets
			    in
			    staking := false;
			    output_byte stdout 83; (*** Report Hit With Storage ***)
			    let c = (stdout,None) in
			    let c = seo_int64 seoc !stktm c in
			    let c = seo_hashval seoc stkaddr c in
			    let c = seo_hashval seoc h c in
			    let c = seo_postor seoc (PostorDoc(gamma,nonce,th,d,h)) c in
			    seocf c;
			    flush stdout
			  with Not_found -> () (*** not a hit at all ***)
		      end
		  end)
	      !stkassets;
	    stktm := Int64.add !stktm 1L
	  done
  done;;

main();;
