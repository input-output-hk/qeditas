(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Mathdata
open Assets
open Tx

val datadir : unit -> string

val reward_maturation : int64
val reward_locktime : int64 -> int64

val coinage : int64 -> int64 -> obligation -> int64 -> big_int

type hlist = HHash of hashval | HNil | HCons of asset * hlist | HConsH of hashval * hlist

val hlist_hashroot : hlist -> hashval option

type nehlist = NehHash of hashval | NehCons of asset * hlist | NehConsH of hashval * hlist

val nehlist_hlist : nehlist -> hlist

val nehlist_hashroot : nehlist -> hashval

type ctree =
  | CLeaf of bool list * nehlist
  | CHash of hashval
  | CLeft of ctree
  | CRight of ctree
  | CBin of ctree * ctree

val ctree_hashroot : ctree -> hashval
val octree_hashroot : ctree option -> hashval option

val ctree_lookup_asset : hashval -> ctree -> bool list -> asset option

exception NotSupported
exception InsufficientInformation
exception GettingRemoteData

val remove_hashed_ctree : hashval -> unit
val archive_unused_ctrees : int64 -> ctree -> ctree -> unit
val remove_unused_ctrees : ctree -> ctree -> unit
val save_hlist_elements : hlist -> hashval option
val save_nehlist_elements : nehlist -> hashval
val save_ctree_elements : ctree -> hashval
val save_ctree : string -> ctree -> unit
val get_hlist_element : hashval -> hlist
val get_nehlist_element : hashval -> nehlist
val get_ctree_element : hashval -> ctree
val ctree_addr : addr -> ctree -> int option -> nehlist option * int

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

val load_expanded_ctree : ctree -> ctree
val load_expanded_octree : ctree option -> ctree option

val full_needed : addr_preasset list -> bool list list
val get_tx_supporting_octree : tx -> ctree option -> ctree option
val get_txl_supporting_octree : tx list -> ctree option -> ctree option

val seo_hlist : (int -> int -> 'a -> 'a) -> hlist -> 'a -> 'a
val sei_hlist : (int -> 'a -> int * 'a) -> 'a -> hlist * 'a

val seo_nehlist : (int -> int -> 'a -> 'a) -> nehlist -> 'a -> 'a
val sei_nehlist : (int -> 'a -> int * 'a) -> 'a -> nehlist * 'a

val seo_ctree : (int -> int -> 'a -> 'a) -> ctree -> 'a -> 'a
val sei_ctree : (int -> 'a -> int * 'a) -> 'a -> ctree * 'a

val print_hlist : hlist -> unit
val print_hlist_to_buffer : Buffer.t -> int64 -> hlist -> unit
val print_ctree : ctree -> unit
val print_ctree_all : ctree -> unit

