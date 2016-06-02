(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Db
open Mathdata

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

val assetid : asset -> hashval
val assetbday : asset -> int64
val assetobl : asset -> obligation
val assetpre : asset -> preasset

val hashobligation : obligation -> hashval option
val hashpreasset : preasset -> hashval
val hashasset : asset -> hashval

type addr_assetid = addr * hashval
type addr_preasset = addr * (obligation * preasset)
type addr_asset = addr * asset

val hash_addr_assetid : addr_assetid -> hashval
val hash_addr_preasset : addr_preasset -> hashval
val hash_addr_asset : addr_asset -> hashval

val new_assets : int64 -> addr -> addr_preasset list -> hashval -> int32 -> asset list
val remove_assets : asset list -> hashval list -> asset list
val get_spent : addr -> addr_assetid list -> hashval list
val add_vout : int64 -> hashval -> addr_preasset list -> int32 -> addr_asset list
val asset_value : int64 -> asset -> int64 option
val asset_value_sum : int64 -> asset list -> int64
val output_signaspec_uses_objs : addr_preasset list -> (termaddr * termaddr) list
val output_signaspec_uses_props : addr_preasset list -> (termaddr * termaddr) list
val output_doc_uses_objs : addr_preasset list -> (termaddr * termaddr) list
val output_doc_uses_props : addr_preasset list -> (termaddr * termaddr) list
val output_creates_objs : addr_preasset list -> (hashval option * hashval * hashval) list
val output_creates_props : addr_preasset list -> (hashval option * hashval) list
val output_creates_neg_props : addr_preasset list -> (hashval option * hashval) list
val rights_out_obj : addr_preasset list -> termaddr -> int64
val rights_out_prop : addr_preasset list -> termaddr -> int64
val count_obj_rights : asset list -> termaddr -> int64
val count_prop_rights : asset list -> termaddr -> int64
val count_rights_used : (termaddr * termaddr) list -> termaddr -> int
val obj_rights_mentioned : addr_preasset list -> termaddr list
val prop_rights_mentioned : addr_preasset list -> termaddr list
val rights_mentioned : addr_preasset list -> termaddr list
val units_sent_to_addr : addr -> addr_preasset list -> int64
val out_cost : addr_preasset list -> int64

val seo_obligation : (int -> int -> 'a -> 'a) -> obligation -> 'a -> 'a
val sei_obligation : (int -> 'a -> int * 'a) -> 'a -> obligation * 'a

val seo_preasset : (int -> int -> 'a -> 'a) -> preasset -> 'a -> 'a
val sei_preasset : (int -> 'a -> int * 'a) -> 'a -> preasset * 'a

val seo_asset : (int -> int -> 'a -> 'a) -> asset -> 'a -> 'a
val sei_asset : (int -> 'a -> int * 'a) -> 'a -> asset * 'a

val seo_addr_assetid : (int -> int -> 'a -> 'a) -> addr_assetid -> 'a -> 'a
val sei_addr_assetid : (int -> 'a -> int * 'a) -> 'a -> addr_assetid * 'a

val seo_addr_preasset : (int -> int -> 'a -> 'a) -> addr_preasset -> 'a -> 'a
val sei_addr_preasset : (int -> 'a -> int * 'a) -> 'a -> addr_preasset * 'a

val seo_addr_asset : (int -> int -> 'a -> 'a) -> addr_asset -> 'a -> 'a
val sei_addr_asset : (int -> 'a -> int * 'a) -> 'a -> addr_asset * 'a

module DbAsset :
    sig
      val dbget : Hash.hashval -> asset
      val dbexists : Hash.hashval -> bool
      val dbput : Hash.hashval -> asset -> unit
      val dbdelete : Hash.hashval -> unit
    end

exception GettingRemoteData

val get_asset : hashval -> asset
