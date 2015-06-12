(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Mathdata
open Assets
open Signat
open Tx
open Ctre
open Ctregraft

type targetinfo = unit (*** to do ***)

type por =
  | PorTrm of termaddr * hashval * tm
  | PorDoc of pubaddr * hashval * pdoc

type blockheader = {
    prevblockhash : hashval option;
    newtheoryroot : hashval option;
    newsignaroot : hashval option;
    newledgerroot : hashval;
    stake : int64;
    stakeaddr : p2pkhaddr;
    stakeassetid : hashval;
    retrievable : por option;
    timestamp : int64;
    tinfo : targetinfo;
    prevledger : ctree;
    blocksignat : signat;
    blocksignatrecid : int;
    blocksignatfcomp : bool;
  }

type blockdelta = {
    stakeoutput : addr_preasset list;
    totalfees : int64;
    prevledgergraft : cgraft;
    blockdelta_stxl : stx list
  }

type block = blockheader * blockdelta

val coinstake : block -> tx

val hash_blockheader : blockheader -> hashval

val valid_blockheader : int64 -> blockheader -> bool

val ctree_of_block : block -> ctree

val tx_of_block : block -> tx

val valid_block : ttree option -> stree option -> int64 -> block -> bool

type blockchain = block * block list
type blockheaderchain = blockheader * blockheader list

val blockchain_headers : blockchain -> blockheaderchain

val ledgerroot_of_blockchain : blockchain -> hashval

val valid_blockchain : int64 -> blockchain -> bool

val valid_blockheaderchain : int64 -> blockheaderchain -> bool


