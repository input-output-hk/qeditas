(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Mathdata
open Assets
open Tx

val reward_maturation : int64
val reward_locktime : int64 -> int64

val coinage : int64 -> int64 -> obligation -> int64 -> big_int

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

type rframe =
  | RFHash
  | RFAll
  | RFLeaf of bool list * int option
  | RFBin of rframe * rframe

val normalize_frame : frame -> rframe
val rframe_lub : rframe -> rframe -> rframe

type ctree =
  | CLeaf of bool list * nehlist
  | CHash of hashval
  | CAbbrev of hashval * hashval
  | CLeft of ctree
  | CRight of ctree
  | CBin of ctree * ctree

val hashctree : ctree -> hashval
val ctree_hashroot : ctree -> hashval
val octree_hashroot : ctree option -> hashval option

val ctree_lookup_asset : hashval -> ctree -> bool list -> asset option

exception NotSupported

val remove_hashed_ctree : hashval -> unit
val archive_unused_ctrees : int64 -> ctree -> ctree -> unit
val remove_unused_ctrees : ctree -> ctree -> unit
val ctree_pre : bool list -> ctree -> int -> ctree option * int
val ctree_addr : addr -> ctree -> ctree option * int
val frame_filter_ctree : frame -> ctree -> ctree
val frame_filter_octree : frame -> ctree option -> ctree option
val rframe_filter_ctree : rframe -> ctree -> ctree
val rframe_filter_octree : rframe -> ctree option -> ctree option
val lookup_all_ctree_root_abbrevs : hashval -> (hashval * hashval) list
val lookup_frame_ctree_root_abbrev : hashval -> hashval -> hashval
val get_ctree_abbrev : hashval -> ctree
val load_root_abbrevs_index : unit -> unit

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

val seo_rframe : (int -> int -> 'a -> 'a) -> rframe -> 'a -> 'a
val sei_rframe : (int -> 'a -> int * 'a) -> 'a -> rframe * 'a

val seo_ctree : (int -> int -> 'a -> 'a) -> ctree -> 'a -> 'a
val sei_ctree : (int -> 'a -> int * 'a) -> 'a -> ctree * 'a

val print_hlist : hlist -> unit
val print_hlist_to_buffer : Buffer.t -> int64 -> hlist -> unit
val print_ctree : ctree -> unit
val print_ctree_all : ctree -> unit

val localframe : frame ref
val localframehash : hashval ref
val wrap_frame : frame -> frame
val hashframe : frame -> hashval
val frame_add_leaf : frame -> addr -> int option -> frame
val frame_set_hash_pos : frame -> bool list -> frame
val frame_set_abbrev_pos : frame -> bool list -> frame
val frame_set_abbrev_level : frame -> int -> frame
val frame_set_all_pos : frame -> bool list -> frame

val build_rframe_to_req : frame -> ctree -> rframe
val split_rframe_for_reqs : int -> rframe -> rframe list
