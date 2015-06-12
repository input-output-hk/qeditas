(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash

type 'a htree =
  | HLeaf of 'a
  | HBin of 'a htree option * 'a htree option

val htree_lookup : bool list -> 'a htree -> 'a option
val htree_create : bool list -> 'a -> 'a htree
val htree_insert : 'a htree -> bool list -> 'a -> 'a htree
val ohtree_hashroot : ('a -> hashval option) -> int -> 'a htree option -> hashval option

