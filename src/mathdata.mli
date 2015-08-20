(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** Significant portions of this code consists of modified from the
 proof checker Egal - Copyright (c) 2014 Chad E Brown, MIT software license.
 The main difference in the syntax is Qeditas provides explicit support for type variables.
 ***)

open Hash
open Htree

(*** TpVar x is the de Bruijn index x as a type variable with corresponding binder TpAll. ***)
type tp = TpVar of int | Prop | Base of int | Ar of tp * tp | TpAll of tp

type tm =
  | DB of int
  | TmH of hashval
  | Prim of int
  | Ap of tm * tm
  | Lam of tp * tm
  | Imp of tm * tm
  | All of tp * tm
  | TTpAp of tm * tp
  | TTpLam of tm
  | TTpAll of tm

type pf =
  | Gpa of hashval
  | Hyp of int
  | Known of hashval
  | PTmAp of pf * tm
  | PPfAp of pf * pf
  | PLam of tm * pf
  | TLam of tp * pf
  | PTpAp of pf * tp
  | PTpLam of pf

type theoryitem =
  | ThyPrim of tp
  | ThyDef of tp * tm
  | ThyAxiom of tm

type theoryspec = theoryitem list

type theory = tp list * hashval list

type signaitem =
  | SignaSigna of hashval
  | SignaParam of hashval * tp
  | SignaDef of tp * tm
  | SignaKnown of tm

type signaspec = signaitem list

type gsigna = (hashval * tp * tm option) list * (hashval * tm) list

type signa = hashval list * gsigna

type docitem =
  | DocSigna of hashval
  | DocParam of hashval * tp
  | DocDef of tp * tm
  | DocKnown of tm
  | DocConj of tm
  | DocPfOf of tm * pf

type doc = docitem list

(** ** pdoc: partical doc, approximating a doc with enough information to compute the hashroot **)
type pdoc =
  | PDocNil
  | PDocHash of hashval
  | PDocSigna of hashval * pdoc
  | PDocParam of hashval * tp * pdoc
  | PDocParamHash of hashval * pdoc
  | PDocDef of tp * tm * pdoc
  | PDocDefHash of hashval * pdoc
  | PDocKnown of tm * pdoc
  | PDocConj of tm * pdoc
  | PDocPfOf of tm * pf * pdoc
  | PDocPfOfHash of hashval * pdoc

(** * serialization code ***)

val seo_tp : (int -> int -> 'a -> 'a) -> tp -> 'a -> 'a
val sei_tp : (int -> 'a -> int * 'a) -> 'a -> tp * 'a

val tp_to_str : tp -> string
val hashtp : tp -> hashval
val str_to_tp : string -> tp

val seo_tm : (int -> int -> 'a -> 'a) -> tm -> 'a -> 'a
val sei_tm : (int -> 'a -> int * 'a) -> 'a -> tm * 'a

val tm_to_str : tm -> string
val hashtm : tm -> hashval
val str_to_tm : string -> tm

val seo_pf : (int -> int -> 'a -> 'a) -> pf -> 'a -> 'a
val sei_pf : (int -> 'a -> int * 'a) -> 'a -> pf * 'a

val pf_to_str : pf -> string
val hashpf : pf -> hashval
val str_to_pf : string -> pf

val seo_theoryspec : (int -> int -> 'a -> 'a) -> theoryspec -> 'a -> 'a
val sei_theoryspec : (int -> 'a -> int * 'a) -> 'a -> theoryspec * 'a

val hashtheoryspec : theoryspec -> hashval

val seo_theory : (int -> int -> 'a -> 'a) -> theory -> 'a -> 'a
val sei_theory : (int -> 'a -> int * 'a) -> 'a -> theory * 'a

val theory_to_str : theory -> string
val str_to_theory : string -> theory

val seo_signaspec : (int -> int -> 'a -> 'a) -> signaspec -> 'a -> 'a
val sei_signaspec : (int -> 'a -> int * 'a) -> 'a -> signaspec * 'a

val hashsignaspec : signaspec -> hashval

val seo_signa : (int -> int -> 'a -> 'a) -> signa -> 'a -> 'a
val sei_signa : (int -> 'a -> int * 'a) -> 'a -> signa * 'a

val signa_to_str : signa -> string
val hashsigna : signa -> hashval
val str_to_signa : string -> signa

val seo_doc : (int -> int -> 'a -> 'a) -> doc -> 'a -> 'a
val sei_doc : (int -> 'a -> int * 'a) -> 'a -> doc * 'a

val hashdoc : doc -> hashval

val seo_pdoc : (int -> int -> 'a -> 'a) -> pdoc -> 'a -> 'a
val sei_pdoc : (int -> 'a -> int * 'a) -> 'a -> pdoc * 'a

val hashpdoc : pdoc -> hashval

(** * computation of hash roots ***)
val tm_hashroot : tm -> hashval
val pf_hashroot : pf -> hashval
val theoryspec_hashroot : theoryspec -> hashval option
val signaspec_hashroot : signaspec -> hashval
val doc_hashroot : doc -> hashval
val pdoc_hashroot : pdoc -> hashval

val theoryspec_theory : theoryspec -> theory

val hashtheory : theory -> hashval option

val signaspec_signa : signaspec -> signa

val hashgsigna : gsigna -> hashval
val hashsigna : signa -> hashval

val theory_burncost : theory -> int64
val theoryspec_burncost : theoryspec -> int64
val signa_burncost : signa -> int64
val signaspec_burncost : signaspec -> int64

val signaspec_uses_objs : signaspec -> (hashval * hashval) list
val signaspec_uses_props : signaspec -> hashval list
val doc_uses_objs : doc -> (hashval * hashval) list
val doc_uses_props : doc -> hashval list
val doc_creates_objs : doc -> (hashval * hashval) list
val doc_creates_props : doc -> hashval list
val doc_creates_neg_props : doc -> hashval list
val signaspec_stp_markers : hashval option -> signaspec -> hashval list
val signaspec_known_markers : hashval option -> signaspec -> hashval list
val doc_stp_markers : hashval option -> doc -> hashval list
val doc_known_markers : hashval option -> doc -> hashval list

(** * htrees to hold theories and signatures **)
type ttree = theory htree
type stree = (hashval option * signa) htree

val ottree_insert : ttree option -> bool list -> theory -> ttree
val ostree_insert : stree option -> bool list -> hashval option -> signa -> stree

val ottree_hashroot : ttree option -> hashval option
val ostree_hashroot : stree option -> hashval option

val ottree_lookup : ttree option -> hashval option -> theory

(** * operations including type checking and proof checking ***)

exception CheckingFailure
exception NonNormalTerm
exception BetaLimit
exception TermLimit

val beta_count : int ref
val term_count : int ref

val check_theoryspec : theoryspec -> theory * gsigna

val check_signaspec :
    (hashval option -> hashval -> tp -> bool)
  -> (hashval option -> hashval -> bool)
  -> hashval option -> theory -> stree option -> signaspec -> gsigna

val check_doc :
    (hashval option -> hashval -> tp -> bool)
  -> (hashval option -> hashval -> bool)
  -> hashval option -> theory -> stree option -> doc -> gsigna
