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

val set_genesis_stakemods : string -> unit
val genesiscurrentstakemod : stakemod ref
val genesisfuturestakemod : stakemod ref
val genesisledgerroot : hashval ref
val genesistarget : big_int ref

val stakemod_pushbit : bool -> stakemod -> stakemod
val stakemod_lastbit : stakemod -> bool
val stakemod_firstbit : stakemod -> bool

type targetinfo = stakemod * stakemod * big_int

val rewfn : int64 -> int64
val hitval : int64 -> hashval -> stakemod -> big_int

type postor =
  | PostorTrm of hashval option * tm * tp * hashval
  | PostorDoc of payaddr * hashval * hashval option * pdoc * hashval

type blockheaderdata = {
    prevblockhash : hashval option;
    newtheoryroot : hashval option;
    newsignaroot : hashval option;
    newledgerroot : hashval;
    stakeaddr : p2pkhaddr;
    stakeassetid : hashval;
    stored : postor option;
    timestamp : int64;
    deltatime : int32;
    tinfo : targetinfo;
    prevledger : ctree;
  }

type blockheadersig = {
    blocksignat : signat;
    blocksignatrecid : int;
    blocksignatfcomp : bool;
  }

type blockheader = blockheaderdata * blockheadersig

val seo_blockheader : (int -> int -> 'a -> 'a) -> blockheader -> 'a -> 'a
val sei_blockheader : (int -> 'a -> int * 'a) -> 'a -> blockheader * 'a

type poforfeit = blockheader * blockheader * blockheaderdata list * blockheaderdata list * int64 * hashval list

type blockdelta = {
    stakeoutput : addr_preasset list;
    forfeiture : poforfeit option;
    prevledgergraft : cgraft;
    blockdelta_stxl : stx list
  }

type block = blockheader * blockdelta

(*** a partial representation of the block delta using hashvals in place of stxs ***)
type blockdeltah = addr_preasset list * poforfeit option * cgraft * hashval list

val seo_blockdeltah : (int -> int -> 'a -> 'a) -> blockdeltah -> 'a -> 'a
val sei_blockdeltah : (int -> 'a -> int * 'a) -> 'a -> blockdeltah * 'a

val coinstake : block -> tx

val check_hit_a : int64 -> int64 -> obligation -> int64
  -> targetinfo -> int64 -> hashval -> p2pkhaddr -> postor option -> bool
val check_hit : int64 -> blockheaderdata -> int64 -> obligation -> int64 -> bool

val hash_blockheaderdata : blockheaderdata -> hashval

val valid_blockheader : int64 -> blockheader -> bool

val ctree_of_block : block -> ctree

val txl_of_block : block -> tx list

val retarget : big_int -> int32 -> big_int

val valid_block : ttree option -> stree option -> int64 -> block -> bool

val blockheader_succ : blockheader -> blockheader -> bool

type blockchain = block * block list
type blockheaderchain = blockheader * blockheader list

val blockchain_headers : blockchain -> blockheaderchain

val ledgerroot_of_blockchain : blockchain -> hashval

val valid_blockchain : int64 -> blockchain -> bool

val valid_blockheaderchain : int64 -> blockheaderchain -> bool
