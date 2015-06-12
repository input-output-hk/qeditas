(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Big_int
open Hash
open Mathdata
open Assets
open Script

type tx = addr_assetid list * addr_preasset list

val hashtx : tx -> hashval
val tx_inputs : tx -> addr_assetid list
val tx_outputs : tx -> addr_preasset list

val no_dups : 'a list -> bool
val tx_inputs_valid : addr_assetid list -> bool
val tx_outputs_valid : addr_preasset list -> bool
val tx_valid : tx -> bool

type stx = tx * (gensignat list * gensignat list)

val tx_signatures_valid : int64 -> asset list -> stx -> bool

val txout_update_ottree : addr_preasset list -> ttree option -> ttree option
val txout_update_ostree : addr_preasset list -> stree option -> stree option
