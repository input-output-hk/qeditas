(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash
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


