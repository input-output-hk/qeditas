(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Big_int
open Mathdata
open Assets
open Signat
open Tx
open Ctre
open Ctregraft

type stakemod = int64 * int64 * int64 * int64

type targetinfo = stakemod * stakemod * big_int

type postor =
  | PostorTrm of hashval option * tm * tp * hashval
  | PostorDoc of payaddr * hashval * hashval option * pdoc * hashval

type blockheader = {
    prevblockhash : hashval option;
    newtheoryroot : hashval option;
    newsignaroot : hashval option;
    newledgerroot : hashval;
    stake : int64;
    stakeaddr : p2pkhaddr;
    stakeassetid : hashval;
    stored : postor option;
    deltatime : int32;
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


