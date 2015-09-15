(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash
open Assets
open Tx
open Ctre

type cgraft = (hashval * ctree) list

let rec cgraft_valid g =
  match g with
  | [] -> true
  | (h,tr)::g' -> ctree_hashroot tr = h && cgraft_valid g'

let rec cgraft_assoc g k =
  match g with
  | [] -> CHash(k)
  | (h,tr)::g' -> if h = k then tr else cgraft_assoc g' k

let rec ctree_cgraft g tr =
  match tr with
  | CHash(h) -> cgraft_assoc g h
  | CLeft(trl) -> CLeft(ctree_cgraft g trl)
  | CRight(trr) -> CRight(ctree_cgraft g trr)
  | CBin(tlr,trr) -> CBin(ctree_cgraft g tlr,ctree_cgraft g trr)
  | _ -> tr

let rec factor_ctree_cgraft n inpl outpl full c =
  if n > 0 then
    begin
      if inpl = [] && outpl = [] && full = [] then
	let ch = ctree_hashroot c in
	(CHash(ch),[(ch,c)])
      else
	begin
	  match c with
	  | CLeft(c0) ->
	      let (c0a,g0) =
		factor_ctree_cgraft (n-1)
		  (strip_bitseq_false inpl)
		  (strip_bitseq_false0 outpl)
		  (strip_bitseq_false0 full)
		  c0
	      in
	      (CLeft(c0a),g0)
	  | CRight(c1) ->
	      let (c1a,g1) =
		factor_ctree_cgraft (n-1)
		  (strip_bitseq_true inpl)
		  (strip_bitseq_true0 outpl)
		  (strip_bitseq_true0 full)
		  c1
	      in
	      (CRight(c1a),g1)
	  | CBin(c0,c1) ->
	      let (c0a,g0) =
		factor_ctree_cgraft (n-1)
		  (strip_bitseq_false inpl)
		  (strip_bitseq_false0 outpl)
		  (strip_bitseq_false0 full)
		  c0
	      in
	      let (c1a,g1) =
		factor_ctree_cgraft (n-1)
		  (strip_bitseq_true inpl)
		  (strip_bitseq_true0 outpl)
		  (strip_bitseq_true0 full)
		  c1
	      in
	      (CBin(c0a,c1a),g0 @ g1)
	  | CAbbrev(hr,ha) ->
	      factor_ctree_cgraft n inpl outpl full (get_ctree_abbrev ha)
	  | CHash(h) -> (*** If we reach this point, the ctree does not support the tx, contrary to assumption. ***)
	      raise (Failure("ctree does not support the tx"))
	  | _ -> (c,[])
	end
    end
  else if full = [] then
    begin
      match c with
      | CLeaf([],_) -> (c,[])
      | _ -> raise (Failure "impossible")
    end
  else (*** At this point we are necessarily at a leaf. However, if the full hlist is not here, then it will not be fully supported. Not checking since we assume c supported before calling this. ***)
    (c,[])
  
let factor_tx_ctree_cgraft (inpl,outpl) c =
  factor_ctree_cgraft
    162
    (List.map (fun (alpha,z) -> (addr_bitseq alpha,z)) inpl)
    (List.map (fun (alpha,(_,_)) -> addr_bitseq alpha) outpl)
    (full_needed outpl)
    c

let factor_inputs_ctree_cgraft inpl c =
  factor_ctree_cgraft
    162
    (List.map (fun (alpha,z) -> (addr_bitseq alpha,z)) inpl)
    [] []
    c

let seo_cgraft o g c = seo_list (seo_prod seo_hashval seo_ctree) o g c
let sei_cgraft i c = sei_list (sei_prod sei_hashval sei_ctree) i c
