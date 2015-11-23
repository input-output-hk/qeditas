(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash
open Mathdata

(*** If the obligation is Some(alpha,n,r), then the way to spend the asset is for alpha to sign after block n.
 If r is true then the asset was a reward and can be forfeited as a consequence of double signing.
 ***)
type obligation = (payaddr * int64 * bool) option

type preasset =
  | Currency of int64
  | Bounty of int64
  | OwnsObj of payaddr * int64 option
  | OwnsProp of payaddr * int64 option
  | OwnsNegProp
  | RightsObj of termaddr * int64
  | RightsProp of termaddr * int64
  | Marker
  | TheoryPublication of payaddr * hashval * theoryspec
  | SignaPublication of payaddr * hashval * hashval option * signaspec
  | DocPublication of payaddr * hashval * hashval option * doc

(*** asset is (assetid,birthday,obligation,preasset) ***)
type asset = hashval * int64 * obligation * preasset

let assetid ((h,bh,obl,u):asset) : hashval = h
let assetobl ((h,bh,obl,u):asset) : obligation = obl
let assetpre ((h,bh,obl,u):asset) : preasset = u

let hashpreasset u =
  match u with
  | Currency(v) -> hashtag (hashint64 v) 256l
  | Bounty(v) -> hashtag (hashint64 v) 257l
  | OwnsObj(a,None) -> hashtag (hashpayaddr a) 258l
  | OwnsObj(a,Some(v)) -> hashtag (hashpair (hashpayaddr a) (hashint64 v)) 259l
  | OwnsProp(a,None) -> hashtag (hashpayaddr a) 260l
  | OwnsProp(a,Some(v)) -> hashtag (hashpair (hashpayaddr a) (hashint64 v)) 261l
  | OwnsNegProp -> hashint32 262l
  | RightsObj(a,v) -> hashtag (hashpair (hashtermaddr a) (hashint64 v)) 263l
  | RightsProp(a,v) -> hashtag (hashpair (hashtermaddr a) (hashint64 v)) 264l
  | Marker -> hashint32 265l
  | TheoryPublication(a,nonce,ths) -> hashtag (hashpair (hashpayaddr a) (hashopair1 nonce (hashtheory (theoryspec_theory ths)))) 266l (*** this only ensures the compiled theory gets a unique hash value ***)
  | SignaPublication(a,nonce,th,s) -> hashtag (hashpair (hashpayaddr a) (hashpair nonce (hashopair2 th (hashsigna (signaspec_signa s))))) 267l (*** this only ensures the compiled signature gets a unique hash value ***)
  | DocPublication(a,nonce,th,d) -> hashtag (hashpair (hashpayaddr a) (hashpair nonce (hashopair2 th (hashdoc d)))) 268l

let hashobligation (x:obligation) : hashval option =
  match x with
  | None -> None
  | Some(a,n,r) -> Some(hashpair (hashpayaddr a) (hashtag (hashint64 n) (if r then 1025l else 1024l)))

let hashasset a =
  let (h,bh,obl,u) = a in
  hashopair1 (hashpair h (hashpair (hashint64 bh) (hashpreasset u))) (hashobligation obl)

type addr_assetid = addr * hashval
type addr_preasset = addr * (obligation * preasset)
type addr_asset = addr * asset

let hash_addr_assetid (alpha,h) = hashpair (hashaddr alpha) h
let hash_addr_preasset (alpha,(obl,u)) = hashpair (hashaddr alpha) (hashopair2 (hashobligation obl) (hashpreasset u))
let hash_addr_asset (alpha,a) = hashpair (hashaddr alpha) (hashasset a)

let rec new_assets bday alpha aul txh i : asset list =
  match aul with
  | [] -> []
  | (beta,(obl,u))::aur when beta = alpha ->
      (hashpair txh (hashint32 i),bday,obl,u)::new_assets bday alpha aur txh (Int32.add i 1l)
  | _::aur -> new_assets bday alpha aur txh (Int32.add i 1l)

let rec remove_assets al spent : asset list =
  match al with
  | [] -> []
  | a::ar when List.mem (assetid a) spent -> remove_assets ar spent
  | a::ar -> a::remove_assets ar spent

let rec get_spent alpha inpl : hashval list =
  match inpl with
  | [] -> []
  | (beta,a)::inpr when alpha = beta -> a::get_spent alpha inpr
  | (beta,a)::inpr -> get_spent alpha inpr

let rec add_vout bday txh outpl i =
  match outpl with
  | [] -> []
  | (alpha,(obl,u))::outpr -> (alpha,(hashpair txh (hashint32 i),bday,obl,u))::add_vout bday txh outpr (Int32.add i 1l)

let preasset_value u =
  match u with
  | Currency v -> Some v
  | Bounty v -> Some v
  | _ -> None

let asset_value u = preasset_value (assetpre u)

let asset_value_sum al =
  List.fold_right Int64.add (List.map (fun a -> match asset_value a with Some v -> v | None -> 0L) al) 0L

let rec output_signaspec_uses_objs (outpl:addr_preasset list) : (termaddr * termaddr) list =
  match outpl with
  | (_,(_,SignaPublication(_,_,th,d)))::outpr ->
      List.map (fun (h,tph) -> (h,hashtag (hashopair2 th (hashpair h tph)) 32l)) (signaspec_uses_objs d)
      @ output_signaspec_uses_objs outpr
  | _::outpr -> output_signaspec_uses_objs outpr
  | [] -> []

let rec output_signaspec_uses_props (outpl:addr_preasset list) : (termaddr * termaddr) list =
  match outpl with
  | (_,(_,SignaPublication(_,_,th,d)))::outpr ->
      List.map (fun h -> (h,hashtag (hashopair2 th h) 33l)) (signaspec_uses_props d)
      @ output_signaspec_uses_props outpr
  | _::outpr -> output_signaspec_uses_props outpr
  | [] -> []

let rec output_doc_uses_objs (outpl:addr_preasset list) : (termaddr * termaddr) list =
  match outpl with
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      List.map (fun (h,tph) -> (h,hashtag (hashopair2 th (hashpair h tph)) 32l)) (doc_uses_objs d)
      @ output_doc_uses_objs outpr
  | _::outpr -> output_doc_uses_objs outpr
  | [] -> []

let rec output_doc_uses_props (outpl:addr_preasset list) : (termaddr * termaddr) list =
  match outpl with
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      List.map (fun h -> (h,hashtag (hashopair2 th h) 33l)) (doc_uses_props d)
      @ output_doc_uses_props outpr
  | _::outpr -> output_doc_uses_props outpr
  | [] -> []

let rec output_creates_objs (outpl:addr_preasset list) : (hashval option * hashval * hashval) list =
  match outpl with
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      List.map (fun (h,k) -> (th,h,k)) (doc_creates_objs d) @ output_creates_objs outpr
  | _::outpr -> output_creates_objs outpr
  | [] -> []

let rec output_creates_props (outpl:addr_preasset list) : (hashval option * hashval) list =
  match outpl with
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      List.map (fun h -> (th,h)) (doc_creates_props d) @ output_creates_props outpr
  | (_,(_,TheoryPublication(_,_,d)))::outpr -> (*** Axioms created by theories also need to be considered "created" so they will be given owners when published. ***)
      let (pl,kl) = theoryspec_theory d in
      let th = hashtheory (pl,kl) in
      List.map (fun h -> (th,h)) kl @ output_creates_props outpr
  | _::outpr -> output_creates_props outpr
  | [] -> []

let rec output_creates_neg_props (outpl:addr_preasset list) : (hashval option * hashval) list =
  match outpl with
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      List.map (fun h -> (th,h)) (doc_creates_neg_props d) @ output_creates_neg_props outpr
  | _::outpr -> output_creates_neg_props outpr
  | [] -> []

let rec output_markers outpl =
  match outpl with
  | (_,(_,SignaPublication(_,_,th,d)))::outpr ->
      signaspec_stp_markers th d @ signaspec_known_markers th d @ output_markers outpr
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      doc_stp_markers th d @ doc_known_markers th d @ output_markers outpr
  | _::outpr -> output_markers outpr
  | [] -> []

let rec rights_out_obj outpl alpha =
  match outpl with
  | (_,(_,RightsObj(beta,n)))::outpr when alpha = beta -> Int64.add n (rights_out_obj outpr alpha)
  | _::outpr -> rights_out_obj outpr alpha
  | [] -> 0L

let rec rights_out_prop outpl alpha =
  match outpl with
  | (_,(_,RightsProp(beta,n)))::outpr when alpha = beta -> Int64.add n (rights_out_prop outpr alpha)
  | _::outpr -> rights_out_prop outpr alpha
  | [] -> 0L

let rec count_obj_rights al alpha =
  match al with
  | (_,_,_,RightsObj(beta,n))::ar when alpha = beta -> Int64.add n (count_obj_rights ar alpha)
  | _::ar -> count_obj_rights ar alpha
  | [] -> 0L

let rec count_prop_rights al alpha =
  match al with
  | (_,_,_,RightsProp(beta,n))::ar when alpha = beta -> Int64.add n (count_prop_rights ar alpha)
  | _::ar -> count_prop_rights ar alpha
  | [] -> 0L

let rec count_rights_used bl alpha =
  match bl with
  | (beta1,beta2)::br when beta1 = alpha || beta2 = alpha -> 1+count_rights_used br alpha
  | _::br -> count_rights_used br alpha
  | [] -> 0

let rec obj_rights_mentioned_aux outpl r =
  match outpl with
  | (beta,(obl,RightsObj(alpha,n)))::outpr ->
      obj_rights_mentioned_aux outpr (alpha::r)
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      let duo = doc_uses_objs d in
      obj_rights_mentioned_aux outpr
	(List.map (fun (h,tph) -> h) duo
	 @ List.map (fun (h,tph) -> hashtag (hashopair2 th (hashpair h tph)) 32l) duo
	 @ r)
  | _::outpr -> obj_rights_mentioned_aux outpr r
  | [] -> r

let obj_rights_mentioned outpl = obj_rights_mentioned_aux outpl []

let rec prop_rights_mentioned_aux outpl r =
  match outpl with
  | (beta,(obl,RightsProp(alpha,n)))::outpr ->
      prop_rights_mentioned_aux outpr (alpha::r)
  | (_,(_,DocPublication(_,_,th,d)))::outpr ->
      let dup = doc_uses_props d in
      prop_rights_mentioned_aux outpr
	(dup @ List.map (fun h -> hashtag (hashopair2 th h) 33l) dup @ r)
  | _::outpr -> prop_rights_mentioned_aux outpr r
  | [] -> r

let prop_rights_mentioned outpl = prop_rights_mentioned_aux outpl []

let rights_mentioned outpl = prop_rights_mentioned_aux outpl (obj_rights_mentioned_aux outpl [])

let rec units_sent_to_addr beta outpl =
  match outpl with
  | (alpha,(None,Currency(u)))::outpr when alpha = beta -> Int64.add u (units_sent_to_addr beta outpr)
  | _::outpr -> units_sent_to_addr beta outpr
  | [] -> 0L

(*** Sum of currency and bounties output as well as the amount that must be burned to publish theories and signatures. ***)
let rec out_cost outpl =
  match outpl with
  | (alpha,(obl,Currency(u)))::outpr -> Int64.add u (out_cost outpr)
  | (alpha,(obl,Bounty(u)))::outpr -> Int64.add u (out_cost outpr)
  | (alpha,(obl,TheoryPublication(_,_,s)))::outpr -> Int64.add (theoryspec_burncost s) (out_cost outpr)
  | (alpha,(obl,SignaPublication(_,_,_,s)))::outpr -> Int64.add (signaspec_burncost s) (out_cost outpr)
  | _::outpr -> out_cost outpr
  | [] -> 0L

(** * serialization **)

let seo_obligation o obl c =
  seo_option (seo_prod3 seo_payaddr seo_int64 seo_bool) o obl c

let sei_obligation i c =
  sei_option (sei_prod3 sei_payaddr sei_int64 sei_bool) i c

let seo_preasset o u c =
  match u with
  | Currency(v) -> (** 000 **)
      let c = o 3 0 c in
      seo_int64 o v c
  | Bounty(v) -> (** 001 **)
      let c = o 3 1 c in
      seo_int64 o v c
  | OwnsObj(alpha,r) -> (** 010 0 **)
      let c = o 4 2 c in
      let c = seo_payaddr o alpha c in
      seo_option seo_int64 o r c
  | OwnsProp(alpha,r) -> (** 010 1 0 **)
      let c = o 5 10 c in
      let c = seo_payaddr o alpha c in
      seo_option seo_int64 o r c
  | OwnsNegProp -> (** 010 1 1 **)
      let c = o 5 26 c in
      c
  | RightsObj(alpha,n) -> (** 011 0 **)
      let c = o 4 3 c in
      let c = seo_termaddr o alpha c in
      seo_int64 o n c
  | RightsProp(alpha,n) -> (** 011 1 **)
      let c = o 4 11 c in
      let c = seo_termaddr o alpha c in
      seo_int64 o n c
  | Marker -> (** 100 **)
      let c = o 3 4 c in
      c
  | TheoryPublication(alpha,h,dl) -> (** 101 **)
      let c = o 3 5 c in
      let c = seo_payaddr o alpha c in
      let c = seo_hashval o h c in
      seo_theoryspec o dl c
  | SignaPublication(alpha,h,th,dl) -> (** 110 **)
      let c = o 3 6 c in
      let c = seo_payaddr o alpha c in
      let c = seo_hashval o h c in
      let c = seo_option seo_hashval o th c in
      seo_signaspec o dl c
  | DocPublication(alpha,h,th,dl) -> (** 111 **)
      let c = o 3 7 c in
      let c = seo_payaddr o alpha c in
      let c = seo_hashval o h c in
      let c = seo_option seo_hashval o th c in
      seo_doc o dl c

let sei_preasset i c =
  let (x,c) = i 3 c in
  if x = 0 then
    let (v,c) = sei_int64 i c in
    (Currency(v),c)
  else if x = 1 then
    let (v,c) = sei_int64 i c in
    (Bounty(v),c)
  else if x = 2 then
    let (y,c) = i 1 c in
    if y = 0 then
      let (alpha,c) = sei_payaddr i c in
      let (r,c) = sei_option sei_int64 i c in
      (OwnsObj(alpha,r),c)
    else
      let (z,c) = i 1 c in
      if z = 0 then
	let (alpha,c) = sei_payaddr i c in
	let (r,c) = sei_option sei_int64 i c in
	(OwnsProp(alpha,r),c)
      else
	(OwnsNegProp,c)
  else if x = 3 then
    let (y,c) = i 1 c in
    let (alpha,c) = sei_termaddr i c in
    let (n,c) = sei_int64 i c in
    if y = 0 then
      (RightsObj(alpha,n),c)
    else
      (RightsProp(alpha,n),c)
  else if x = 4 then
    (Marker,c)
  else if x = 5 then
    let (alpha,c) = sei_payaddr i c in
    let (h,c) = sei_hashval i c in
    let (dl,c) = sei_theoryspec i c in
    (TheoryPublication(alpha,h,dl),c)
  else if x = 6 then
    let (alpha,c) = sei_payaddr i c in
    let (h,c) = sei_hashval i c in
    let (th,c) = sei_option sei_hashval i c in
    let (dl,c) = sei_signaspec i c in
    (SignaPublication(alpha,h,th,dl),c)
  else
    let (alpha,c) = sei_payaddr i c in
    let (h,c) = sei_hashval i c in
    let (th,c) = sei_option sei_hashval i c in
    let (dl,c) = sei_doc i c in
    (DocPublication(alpha,h,th,dl),c)

let seo_asset o a c = seo_prod4 seo_hashval seo_int64 seo_obligation seo_preasset o a c
let sei_asset i c = sei_prod4 sei_hashval sei_int64 sei_obligation sei_preasset i c

let seo_addr_assetid o u c = seo_prod seo_addr seo_hashval o u c
let sei_addr_assetid i c = sei_prod sei_addr sei_hashval i c
let seo_addr_preasset o u c = seo_prod seo_addr (seo_prod seo_obligation seo_preasset) o u c
let sei_addr_preasset i c = sei_prod sei_addr (sei_prod sei_obligation sei_preasset) i c
let seo_addr_asset o a c = seo_prod seo_addr seo_asset o a c
let sei_addr_asset i c = sei_prod sei_addr sei_asset i c
