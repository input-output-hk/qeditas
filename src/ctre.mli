(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Mathdata
open Assets
open Tx

type hlist = HHash of hashval | HNil | HCons of asset * hlist

val hlist_hashroot : hlist -> hashval option

type nehlist = NehHash of hashval | NehCons of asset * hlist

val nehlist_hlist : nehlist -> hlist

val nehlist_hashroot : nehlist -> hashval

type frame =
  | FHash
  | FAbbrev of frame
  | FAll
  | FLeaf of bool list * int option
  | FBin of frame * frame

type ctree =
  | CLeaf of bool list * nehlist
  | CHash of hashval
  | CAbbrev of hashval
  | CLeft of ctree
  | CRight of ctree
  | CBin of ctree * ctree

val ctree_hashroot : ctree -> hashval
val octree_hashroot : ctree option -> hashval option

val ctree_lookup_asset : hashval -> ctree -> bool list -> asset option

exception NotSupported

val get_ctree_abbrev : hashval -> ctree

val strip_bitseq_true : (bool list * 'a) list -> (bool list * 'a) list
val strip_bitseq_false : (bool list * 'a) list -> (bool list * 'a) list
val strip_bitseq_true0 : bool list list -> bool list list
val strip_bitseq_false0 : bool list list -> bool list list

val ctree_lookup_input_assets : addr_assetid list -> ctree -> (addr * asset) list
val ctree_supports_tx : ttree option -> stree option -> int64 -> tx -> ctree -> int64
val ctree_supports_tx_2 : ttree option -> stree option -> int64 -> tx -> (addr * asset) list -> asset list -> ctree -> int64

val tx_octree_trans : int64 -> tx -> ctree option -> ctree option
val txl_octree_trans : int64 -> tx list -> ctree option -> ctree option

val octree_lub : ctree option -> ctree option -> ctree option

val full_needed : addr_preasset list -> bool list list
val get_tx_supporting_octree : tx -> ctree option -> ctree option
val get_txl_supporting_octree : tx list -> ctree option -> ctree option

val seo_hlist : (int -> int -> 'a -> 'a) -> hlist -> 'a -> 'a
val sei_hlist : (int -> 'a -> int * 'a) -> 'a -> hlist * 'a

val seo_nehlist : (int -> int -> 'a -> 'a) -> nehlist -> 'a -> 'a
val sei_nehlist : (int -> 'a -> int * 'a) -> 'a -> nehlist * 'a

val seo_frame : (int -> int -> 'a -> 'a) -> frame -> 'a -> 'a
val sei_frame : (int -> 'a -> int * 'a) -> 'a -> frame * 'a

val seo_ctree : (int -> int -> 'a -> 'a) -> ctree -> 'a -> 'a
val sei_ctree : (int -> 'a -> int * 'a) -> 'a -> ctree * 'a

val print_ctree : ctree -> unit
val print_ctree_all : ctree -> unit
