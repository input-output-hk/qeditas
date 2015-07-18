(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Tx
open Ctre

type cgraft = (hashval * ctree) list

val cgraft_valid : cgraft -> bool
val ctree_cgraft : cgraft -> ctree -> ctree

val factor_tx_ctree_cgraft : tx -> ctree -> ctree * cgraft
