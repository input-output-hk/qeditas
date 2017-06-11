open Hash
open Logic
open Htree

(** ** pdoc: partical doc, approximating a doc with enough information to compute the hashroot **)
type pdoc =
  | PDocNil
  | PDocHash of hashval
  | PDocSigna of hashval * pdoc
  | PDocParam of hashval * stp * pdoc
  | PDocParamHash of hashval * pdoc
  | PDocDef of stp * trm * pdoc
  | PDocDefHash of hashval * pdoc
  | PDocKnown of trm * pdoc
  | PDocConj of trm * pdoc
  | PDocPfOf of trm * pf * pdoc
  | PDocPfOfHash of hashval * pdoc

(** * serialization code ***)

val seo_tp : (int -> int -> 'a -> 'a) -> stp -> 'a -> 'a
val sei_tp : (int -> 'a -> int * 'a) -> 'a -> stp * 'a

val hashtp : stp -> hashval

val seo_tm : (int -> int -> 'a -> 'a) -> trm -> 'a -> 'a
val sei_tm : (int -> 'a -> int * 'a) -> 'a -> trm * 'a

val hashtm : trm -> hashval
val tm_hashroot : trm -> hashval

val seo_pf : (int -> int -> 'a -> 'a) -> pf -> 'a -> 'a
val sei_pf : (int -> 'a -> int * 'a) -> 'a -> pf * 'a

val hashpf : pf -> hashval
val pf_hashroot : pf -> hashval

val seo_theoryspec : (int -> int -> 'a -> 'a) -> theoryspec -> 'a -> 'a
val sei_theoryspec : (int -> 'a -> int * 'a) -> 'a -> theoryspec * 'a
val seo_theory : (int -> int -> 'a -> 'a) -> theory -> 'a -> 'a
val sei_theory : (int -> 'a -> int * 'a) -> 'a -> theory * 'a

val hashtheory : theory -> hashval option

val theoryspec_theory : theoryspec -> theory
val theoryspec_burncost : theoryspec -> int64

val seo_signaspec : (int -> int -> 'a -> 'a) -> signaspec -> 'a -> 'a
val sei_signaspec : (int -> 'a -> int * 'a) -> 'a -> signaspec * 'a
val seo_signa : (int -> int -> 'a -> 'a) -> signa -> 'a -> 'a
val sei_signa : (int -> 'a -> int * 'a) -> 'a -> signa * 'a

val hashsigna : signa -> hashval

val signaspec_signa : signaspec -> signa
val signaspec_burncost : signaspec -> int64

val seo_doc : (int -> int -> 'a -> 'a) -> doc -> 'a -> 'a
val sei_doc : (int -> 'a -> int * 'a) -> 'a -> doc * 'a
val seo_pdoc : (int -> int -> 'a -> 'a) -> pdoc -> 'a -> 'a
val sei_pdoc : (int -> 'a -> int * 'a) -> 'a -> pdoc * 'a


val hashdoc : doc -> hashval
val doc_hashroot : doc -> hashval

val hashpdoc : pdoc -> hashval
val pdoc_hashroot : pdoc -> hashval

val signaspec_uses_objs : signaspec -> (hashval * hashval) list
val signaspec_uses_props : signaspec -> hashval list
val doc_uses_objs : doc -> (hashval * hashval) list
val doc_uses_props : doc -> hashval list
val doc_creates_objs : doc -> (hashval * hashval) list
val doc_creates_props : doc -> hashval list
val doc_creates_neg_props : doc -> hashval list

(** * htrees to hold theories and signatures **)
type ttree = theory htree
type stree = signa htree

val ottree_insert : ttree option -> bool list -> theory -> ttree
val ostree_insert : stree option -> bool list -> signa -> stree

val ottree_hashroot : ttree option -> hashval option
val ostree_hashroot : stree option -> hashval option

val ottree_lookup : ttree option -> hashval option -> theory

exception CheckingFailure
exception NotKnown of hashval option * hashval
exception UnknownTerm of hashval option * hashval * stp
exception UnknownSigna of hashval
exception NonNormalTerm
exception BetaLimit
exception TermLimit

val import_signatures : hashval option -> stree -> hashval list -> gsign -> hashval list -> (gsign * hashval list) option

val print_trm : int -> stp list -> gsign -> trm -> stp list -> unit
val print_tp : int -> stp -> int -> unit
