(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash

type 'a htree =
  | HLeaf of 'a
  | HBin of 'a htree option * 'a htree option

let rec htree_lookup bl ht =
  match bl,ht with
  | [],HLeaf(x) -> Some(x)
  | false::br,HBin(Some(hl),hr) -> htree_lookup br hl
  | true::br,HBin(hl,Some(hr)) -> htree_lookup br hr
  | _,_ -> None

let rec htree_create bl x =
  match bl with
  | [] -> HLeaf(x)
  | false::br -> HBin(Some(htree_create br x),None)
  | true::br -> HBin(None,Some(htree_create br x))

let rec htree_insert ht bl x =
  match bl with
  | [] -> HLeaf(x)
  | false::br ->
      begin
	match ht with
	| HBin(Some(hl),hr) -> HBin(Some(htree_insert hl br x),hr)
	| HBin(None,hr) -> HBin(Some(htree_create br x),hr)
	| _ ->  raise (Failure "bad htree case")
      end
  | true::br ->
      begin
	match ht with
	| HBin(hl,Some(hr)) -> HBin(hl,Some(htree_insert hr br x))
	| HBin(hl,None) -> HBin(hl,Some(htree_create br x))
	| _ ->  raise (Failure "bad htree case")
      end

let rec ohtree_hashroot f n oht =
  if n > 0 then
    match oht with
    | Some(HBin(hl,hr)) -> hashopair (ohtree_hashroot f (n-1) hl) (ohtree_hashroot f (n-1) hr)
    | _ -> None
  else
    match oht with
    | Some(HLeaf(x)) -> f x
    | _ -> None

