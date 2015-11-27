(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** Significant portions of this code consists of modified from the proof checker Egal.
 The main difference in the syntax is Qeditas provides explicit support for type variables.
 ***)

open Ser
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

(** ** tp serialization ***)

let rec seo_tp o m c =
  match m with
  | Ar(m0,m1) -> (*** 00 ***)
      let c = o 2 0 c in
      let c = seo_tp o m0 c in
      let c = seo_tp o m1 c in
      c
  | Prop -> (*** 01 ***)
      o 2 1 c
  | Base(x) when x < 65536 -> (*** 10 ***)
      let c = o 2 2 c in
      seo_varintb o x c
  | Base(_) -> raise (Failure("Invalid base type"))
  | TpVar(x) when x < 65536 -> (*** 11 0 x ***)
      let c = o 3 3 c in
      let c = seo_varintb o x c in
      c
  | TpVar(_) -> raise (Failure("Invalid type variable"))
  | TpAll(a) -> (*** 11 1 ***)
      let c = o 3 7 c in
      let c = seo_tp o a c in
      c

let tp_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_tp seosb m (c,None));
  Buffer.contents c

let hashtp m = hashtag (hash160 (tp_to_str m)) 64l

let rec sei_tp i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tp i c in
    (Ar(m0,m1),c)
  else if b = 1 then
    (Prop,c)
  else if b = 2 then
    let (x,c) = sei_varintb i c in
    (Base(x),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (x,c) = sei_varintb i c in
      (TpVar(x),c)
    else
      let (m0,c) = sei_tp i c in
      (TpAll(m0),c)

(** ** tp list serialization ***)
let seo_tpl o al c = seo_list seo_tp o al c
let sei_tpl i c = sei_list sei_tp i c

let tpl_to_str al =
  let c = Buffer.create 1000 in
  seosbf (seo_tpl seosb al (c,None));
  Buffer.contents c

let hashtpl al =
  if al = [] then
    None
  else
    Some(hashtag (hash160 (tpl_to_str al)) 65l)

(** ** tm serialization ***)
let rec seo_tm o m c =
  match m with
  | TmH(h) -> (*** 000 ***)
      let c = o 3 0 c in
      let c = seo_hashval o h c in
      c
  | DB(x) when x >= 0 && x <= 65535 -> (*** 001 ***)
      let c = o 3 1 c in
      seo_varintb o x c
  | DB(x) ->
      raise (Failure "seo_tm - de Bruijn out of bounds");
  | Prim(x) when x >= 0 && x <= 65535 -> (*** 010 ***)
      let c = o 3 2 c in
      let c = seo_varintb o x c in
      c
  | Prim(x) ->
      raise (Failure "seo_tm - Prim out of bounds");
  | Ap(m0,m1) -> (*** 011 ***)
      let c = o 3 3 c in
      let c = seo_tm o m0 c in
      let c = seo_tm o m1 c in
      c
  | Lam(m0,m1) -> (*** 100 ***)
      let c = o 3 4 c in
      let c = seo_tp o m0 c in
      let c = seo_tm o m1 c in
      c
  | Imp(m0,m1) -> (*** 101 ***)
      let c = o 3 5 c in
      let c = seo_tm o m0 c in
      let c = seo_tm o m1 c in
      c
  | All(m0,m1) -> (*** 110 ***)
      let c = o 3 6 c in
      let c = seo_tp o m0 c in
      let c = seo_tm o m1 c in
      c
  | TTpAp(m0,a) -> (*** 111 0 ***)
      let c = o 4 7 c in
      let c = seo_tm o m0 c in
      let c = seo_tp o a c in
      c
  | TTpLam(m0) -> (*** 111 1 0 ***)
      let c = o 5 15 c in
      let c = seo_tm o m0 c in
      c
  | TTpAll(m0) -> (*** 111 1 1 ***)
      let c = o 5 31 c in
      let c = seo_tm o m0 c in
      c

let tm_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_tm seosb m (c,None));
  Buffer.contents c

let hashtm m = hashtag (hash160 (tm_to_str m)) 66l

let rec sei_tm i c =
  let (x,c) = i 3 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (TmH(h),c)
  else if x = 1 then
    let (z,c) = sei_varintb i c in
    (DB(z),c)
  else if x = 2 then
    let (z,c) = sei_varintb i c in
    (Prim(z),c)
  else if x = 3 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_tm i c in
    (Ap(m0,m1),c)
  else if x = 4 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tm i c in
    (Lam(m0,m1),c)
  else if x = 5 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_tm i c in
    (Imp(m0,m1),c)
  else if x = 6 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tm i c in
    (All(m0,m1),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (m0,c) = sei_tm i c in
      let (a,c) = sei_tp i c in
      (TTpAp(m0,a),c)
    else
      let (y,c) = i 1 c in
      if y = 0 then
	let (m0,c) = sei_tm i c in
	(TTpLam(m0),c)
      else
	let (m0,c) = sei_tm i c in
	(TTpAll(m0),c)

(** ** pf serialization ***)
let rec seo_pf o m c =
  match m with
  | Gpa(h) -> (*** 000 ***)
      let c = o 3 0 c in
      seo_hashval o h c
  | Hyp(x) when x >= 0 && x <= 65535 -> (*** 001 ***)
      let c = o 3 1 c in
      seo_varintb o x c
  | Hyp(x) ->
      raise (Failure "seo_pf - Hypothesis out of bounds");
  | Known(h) -> (*** 010 ***)
      let c = o 3 2 c in
      let c = seo_hashval o h c in
      c
  | PTmAp(m0,m1) -> (*** 011 ***)
      let c = o 3 3 c in
      let c = seo_pf o m0 c in
      let c = seo_tm o m1 c in
      c
  | PPfAp(m0,m1) -> (*** 100 ***)
      let c = o 3 4 c in
      let c = seo_pf o m0 c in
      let c = seo_pf o m1 c in
      c
  | PLam(m0,m1) -> (*** 101 ***)
      let c = o 3 5 c in
      let c = seo_tm o m0 c in
      let c = seo_pf o m1 c in
      c
  | TLam(m0,m1) -> (*** 110 ***)
      let c = o 3 6 c in
      let c = seo_tp o m0 c in
      let c = seo_pf o m1 c in
      c
  | PTpAp(d,a) -> (*** 111 0 ***)
      let c = o 4 7 c in
      let c = seo_pf o d c in
      let c = seo_tp o a c in
      c
  | PTpLam(d) -> (*** 111 1 ***)
      let c = o 4 15 c in
      let c = seo_pf o d c in
      c

let pf_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_pf seosb m (c,None));
  Buffer.contents c

let hashpf m = hashtag (hash160 (pf_to_str m)) 67l

let rec sei_pf i c =
  let (x,c) = i 3 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (Gpa(h),c)
  else if x = 1 then
    let (z,c) = sei_varintb i c in
    (Hyp(z),c)
  else if x = 2 then
    let (z,c) = sei_hashval i c in
    (Known(z),c)
  else if x = 3 then
    let (m0,c) = sei_pf i c in
    let (m1,c) = sei_tm i c in
    (PTmAp(m0,m1),c)
  else if x = 4 then
    let (m0,c) = sei_pf i c in
    let (m1,c) = sei_pf i c in
    (PPfAp(m0,m1),c)
  else if x = 5 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_pf i c in
    (PLam(m0,m1),c)
  else if x = 6 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_pf i c in
    (TLam(m0,m1),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (d,c) = sei_pf i c in
      let (a,c) = sei_tp i c in
      (PTpAp(d,a),c)
    else
      let (d,c) = sei_pf i c in
      (PTpLam(d),c)

(** ** theoryspec serialization ***)
let seo_theoryitem o m c =
  match m with
  | ThyPrim(a) -> (* 0 0 *)
      let c = o 2 0 c in
      seo_tp o a c
  | ThyDef(a,m) -> (* 0 1 *)
      let c = o 2 2 c in
      let c = seo_tp o a c in
      seo_tm o m c
  | ThyAxiom(m) -> (* 1 *)
      let c = o 1 1 c in
      seo_tm o m c

let sei_theoryitem i c =
  let (b,c) = i 1 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (a,c) = sei_tp i c in
      (ThyPrim(a),c)
    else
      let (a,c) = sei_tp i c in
      let (m,c) = sei_tm i c in
      (ThyDef(a,m),c)
  else
    let (m,c) = sei_tm i c in
    (ThyAxiom(m),c)

let seo_theoryspec o dl c = seo_list seo_theoryitem o dl c
let sei_theoryspec i c = sei_list sei_theoryitem i c

let theoryspec_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_theoryspec seosb m (c,None));
  Buffer.contents c

(** ** signaspec serialization ***)
let seo_signaitem o m c =
  match m with
  | SignaSigna(h) -> (** 00 **)
      let c = o 2 0 c in
      seo_hashval o h c
  | SignaParam(h,a) -> (** 01 **)
      let c = o 2 1 c in
      let c = seo_hashval o h c in
      seo_tp o a c
  | SignaDef(a,m) -> (** 10 **)
      let c = o 2 2 c in
      let c = seo_tp o a c in
      seo_tm o m c
  | SignaKnown(m) -> (** 11 **)
      let c = o 2 3 c in
      seo_tm o m c

let sei_signaitem i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (h,c) = sei_hashval i c in
    (SignaSigna(h),c)
  else if b = 1 then
    let (h,c) = sei_hashval i c in
    let (a,c) = sei_tp i c in
    (SignaParam(h,a),c)
  else if b = 2 then
    let (a,c) = sei_tp i c in
    let (m,c) = sei_tm i c in
    (SignaDef(a,m),c)
  else
    let (m,c) = sei_tm i c in
    (SignaKnown(m),c)

let seo_signaspec o dl c = seo_list seo_signaitem o dl c
let sei_signaspec i c = sei_list sei_signaitem i c

let signaspec_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_signaspec seosb m (c,None));
  Buffer.contents c

(** ** doc serialization ***)
let seo_docitem o m c =
  match m with
  | DocSigna(h) -> (** 00 0 **)
      let c = o 3 0 c in
      seo_hashval o h c
  | DocParam(h,a) -> (** 00 1 **)
      let c = o 3 4 c in
      let c = seo_hashval o h c in
      seo_tp o a c
  | DocDef(a,m) -> (** 01 **)
      let c = o 2 1 c in
      let c = seo_tp o a c in
      seo_tm o m c
  | DocKnown(m) -> (** 10 0 **)
      let c = o 3 2 c in
      seo_tm o m c
  | DocConj(m) -> (** 10 1 **)
      let c = o 3 6 c in
      seo_tm o m c
  | DocPfOf(m,d) -> (** 11 **)
      let c = o 2 3 c in
      let c = seo_tm o m c in
      seo_pf o d c

let sei_docitem i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (h,c) = sei_hashval i c in
      (DocSigna(h),c)
    else
      let (h,c) = sei_hashval i c in
      let (a,c) = sei_tp i c in
      (DocParam(h,a),c)
  else if b = 1 then
    let (a,c) = sei_tp i c in
    let (m,c) = sei_tm i c in
    (DocDef(a,m),c)
  else if b = 2 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (m,c) = sei_tm i c in
      (DocKnown(m),c)
    else
      let (m,c) = sei_tm i c in
      (DocConj(m),c)
  else
    let (m,c) = sei_tm i c in
    let (d,c) = sei_pf i c in
    (DocPfOf(m,d),c)

let seo_doc o dl c = seo_list seo_docitem o dl c
let sei_doc i c = sei_list sei_docitem i c

let doc_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_doc seosb m (c,None));
  Buffer.contents c

let hashdoc m = hashtag (hash160 (doc_to_str m)) 70l

(** ** pdoc serialization ***)
let rec seo_pdoc o dl c =
  match dl with
  | PDocNil -> (** 00 0 **)
      o 3 0 c
  | PDocHash(h) -> (** 00 1 **)
      let c = o 3 4 c in
      let c = seo_hashval o h c in
      c
  | PDocSigna(h,dr) -> (** 01 0 **)
      let c = o 3 1 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c
  | PDocParam(h,a,dr) -> (** 01 1 **)
      let c = o 3 5 c in
      let c = seo_hashval o h c in
      let c = seo_tp o a c in
      seo_pdoc o dr c
  | PDocParamHash(h,dr) -> (** 10 0 **)
      let c = o 3 2 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c
  | PDocDef(a,m,dr) -> (** 10 1 0 **)
      let c = o 4 6 c in
      let c = seo_tp o a c in
      let c = seo_tm o m c in
      seo_pdoc o dr c
  | PDocDefHash(h,dr) -> (** 10 1 1 **)
      let c = o 4 14 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c
  | PDocKnown(m,dr) -> (** 11 00 **)
      let c = o 4 3 c in
      let c = seo_tm o m c in
      seo_pdoc o dr c
  | PDocConj(m,dr) -> (** 11 01 **)
      let c = o 4 7 c in
      let c = seo_tm o m c in
      seo_pdoc o dr c
  | PDocPfOf(m,d,dr) -> (** 11 10 **)
      let c = o 4 11 c in
      let c = seo_tm o m c in
      let c = seo_pf o d c in
      seo_pdoc o dr c
  | PDocPfOfHash(h,dr) -> (** 11 11 **)
      let c = o 4 15 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c

let pdoc_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_pdoc seosb m (c,None));
  Buffer.contents c

let hashpdoc m = hashtag (hash160 (pdoc_to_str m)) 71l

let rec sei_pdoc i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      (PDocNil,c)
    else
      let (h,c) = sei_hashval i c in
      (PDocHash(h),c)
  else if b = 1 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocSigna(h,dr),c)
    else
      let (h,c) = sei_hashval i c in
      let (a,c) = sei_tp i c in
      let (dr,c) = sei_pdoc i c in
      (PDocParam(h,a,dr),c)
  else if b = 2 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocParamHash(h,dr),c)
    else
      let (b,c) = i 1 c in
      if b = 0 then
	let (a,c) = sei_tp i c in
	let (m,c) = sei_tm i c in
	let (dr,c) = sei_pdoc i c in
	(PDocDef(a,m,dr),c)
      else
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocDefHash(h,dr),c)
  else
    let (b,c) = i 2 c in
    if b = 0 then
      let (m,c) = sei_tm i c in
      let (dr,c) = sei_pdoc i c in
      (PDocKnown(m,dr),c)
    else if b = 1 then
      let (m,c) = sei_tm i c in
      let (dr,c) = sei_pdoc i c in
      (PDocConj(m,dr),c)
    else if b = 2 then
      let (m,c) = sei_tm i c in
      let (d,c) = sei_pf i c in
      let (dr,c) = sei_pdoc i c in
      (PDocPfOf(m,d,dr),c)
    else
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocPfOfHash(h,dr),c)

(** ** serialization of theories ***)
let seo_theory o (al,kl) c =
  let c = seo_tpl o al c in
  seo_list seo_hashval o kl c

let sei_theory i c =
  let (al,c) = sei_tpl i c in
  let (kl,c) = sei_list sei_hashval i c in
  ((al,kl),c)

let theory_to_str thy =
  let c = Buffer.create 1000 in
  seosbf (seo_theory seosb thy (c,None));
  Buffer.contents c

(** * computation of hash roots ***)
let rec tm_hashroot m =
  match m with
  | TmH(h) -> h
  | Prim(x) -> hashtag (hashint32 (Int32.of_int x)) 96l
  | DB(x) -> hashtag (hashint32 (Int32.of_int x)) 97l
  | Ap(m,n) -> hashtag (hashpair (tm_hashroot m) (tm_hashroot n)) 98l
  | Lam(a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 99l
  | Imp(m,n) -> hashtag (hashpair (tm_hashroot m) (tm_hashroot n)) 100l
  | All(a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 101l
  | TTpAp(m,a) -> hashtag (hashpair (tm_hashroot m) (hashtp a)) 102l
  | TTpLam(m) -> hashtag (tm_hashroot m) 103l
  | TTpAll(m) -> hashtag (tm_hashroot m) 104l

(*** hashroot of negation (m -> False) of the term m ***)
let neg_tm_hashroot m = tm_hashroot (Imp(m,All(Prop,DB(0))))

let rec pf_hashroot d =
  match d with
  | Gpa(h) -> h
  | Known(h) -> hashtag h 128l
  | Hyp(x) -> hashtag (hashint32 (Int32.of_int x)) 129l
  | PTmAp(d,m) -> hashtag (hashpair (pf_hashroot d) (tm_hashroot m)) 130l
  | PPfAp(d,e) -> hashtag (hashpair (pf_hashroot d) (pf_hashroot e)) 131l
  | PLam(m,d) -> hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 132l
  | TLam(a,d) -> hashtag (hashpair (hashtp a) (pf_hashroot d)) 133l
  | PTpAp(d,a) -> hashtag (hashpair (pf_hashroot d) (hashtp a)) 134l
  | PTpLam(d) -> hashtag (pf_hashroot d) 135l

let rec docitem_hashroot d =
  match d with
  | DocSigna(h) -> hashtag h 172l
  | DocParam(h,a) -> hashtag (hashpair h (hashtp a)) 173l
  | DocDef(a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 174l
  | DocKnown(m) -> hashtag (tm_hashroot m) 175l
  | DocConj(m) -> hashtag (tm_hashroot m) 176l
  | DocPfOf(m,d) -> hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 177l

let rec doc_hashroot dl =
  match dl with
  | [] -> hashint32 180l
  | d::dr -> hashtag (hashpair (docitem_hashroot d) (doc_hashroot dr)) 181l

let rec pdoc_hashroot dl =
  match dl with
  | PDocNil -> hashint32 180l
  | PDocHash(h) -> h
  | PDocSigna(h,dr) ->
      hashtag (hashpair (hashtag h 172l)
		 (pdoc_hashroot dr)) 181l
  | PDocParam(h,a,dr) ->
      hashtag (hashpair (hashtag (hashpair h (hashtp a)) 173l)
		 (pdoc_hashroot dr)) 181l
  | PDocParamHash(h,dr) ->
      hashtag (hashpair (hashtag h 173l)
		 (pdoc_hashroot dr)) 181l
  | PDocDef(a,m,dr) ->
      hashtag (hashpair (hashtag (hashpair (hashtp a) (tm_hashroot m)) 174l)
		 (pdoc_hashroot dr)) 181l
  | PDocDefHash(h,dr) ->
      hashtag (hashpair (hashtag h 174l)
		 (pdoc_hashroot dr)) 181l
  | PDocKnown(m,dr) ->
      hashtag (hashpair (hashtag (tm_hashroot m) 175l)
		 (pdoc_hashroot dr)) 181l
  | PDocConj(m,dr) ->
      hashtag (hashpair (hashtag (tm_hashroot m) 176l)
		 (pdoc_hashroot dr)) 181l
  | PDocPfOf(m,d,dr) ->
      hashtag (hashpair (hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 177l)
		 (pdoc_hashroot dr)) 181l
  | PDocPfOfHash(h,dr) ->
      hashtag (hashpair (hashtag h 177l)
		 (pdoc_hashroot dr)) 181l

(** * conversion of theoryspec to theory and signaspec to signa **)
let rec theoryspec_primtps_r dl =
  match dl with
  | [] -> []
  | ThyPrim(a)::dr -> a::theoryspec_primtps_r dr
  | _::dr -> theoryspec_primtps_r dr
  
let theoryspec_primtps dl = List.rev (theoryspec_primtps_r dl)

let rec theoryspec_hashedaxioms dl =
  match dl with
  | [] -> []
  | ThyAxiom(m)::dr -> tm_hashroot m::theoryspec_hashedaxioms dr
  | _::dr -> theoryspec_hashedaxioms dr

let theoryspec_theory thy = (theoryspec_primtps thy,theoryspec_hashedaxioms thy)

let hashtheory (al,kl) =
  hashopair
    (ohashlist (List.map hashtp al))
    (ohashlist kl)

let rec signaspec_signas s =
  match s with
  | [] -> []
  | SignaSigna(h)::r -> h::signaspec_signas r
  | _::r -> signaspec_signas r

let rec signaspec_trms s =
  match s with
  | [] -> []
  | SignaParam(h,a)::r -> (h,a,None)::signaspec_trms r
  | SignaDef(a,m)::r -> (tm_hashroot m,a,Some(m))::signaspec_trms r
  | _::r -> signaspec_trms r

let rec signaspec_knowns s =
  match s with
  | [] -> []
  | SignaKnown(p)::r -> (tm_hashroot p,p)::signaspec_knowns r
  | _::r -> signaspec_knowns r

let signaspec_signa s = (signaspec_signas s,(signaspec_trms s,signaspec_knowns s))

let hashgsigna (tl,kl) =
  hashpair
    (hashlist
       (List.map (fun z ->
	 match z with
	 | (h,a,None) -> hashtag (hashpair h (hashtp a)) 160l
	 | (h,a,Some(m)) -> hashtag (hashpair h (hashpair (hashtp a) (hashtm m))) 161l)
	  tl))
    (hashlist (List.map (fun (k,p) -> (hashpair k (hashtm p))) kl))

let hashsigna (sl,(tl,kl)) = hashpair (hashlist sl) (hashgsigna (tl,kl))

let seo_gsigna o s c =
  seo_prod
    (seo_list (seo_prod3 seo_hashval seo_tp (seo_option seo_tm)))
    (seo_list (seo_prod seo_hashval seo_tm))
    o s c

let sei_gsigna i c =
  sei_prod
    (sei_list (sei_prod3 sei_hashval sei_tp (sei_option sei_tm)))
    (sei_list (sei_prod sei_hashval sei_tm))
    i c

let seo_signa o s c =
  seo_prod (seo_list seo_hashval) seo_gsigna o s c

let sei_signa i c =
  sei_prod (sei_list sei_hashval) sei_gsigna i c

let signa_to_str s =
  let c = Buffer.create 1000 in
  seosbf (seo_signa seosb s (c,None));
  Buffer.contents c

(** * use serializations of theory/signatures to determine the burncost.
 21 zerms (21 billion cants) per byte for each.
 Option: In the protocol this could be the "base" burn cost which is halved every N blocks.
 That way, there wouldn't be a hard limit on the amount of theory/signatures that can be published.
 The N should be chosen so that storage capacity is expected to double in that time.
 **)

let theory_burncost thy =
  Int64.mul 21000000000L (Int64.of_int (String.length (theory_to_str thy)))
  
let theoryspec_burncost s = theory_burncost (theoryspec_theory s)

let signa_burncost s =
  Int64.mul 21000000000L (Int64.of_int (String.length (signa_to_str s)))

let signaspec_burncost s = signa_burncost (signaspec_signa s)

(** * extract which objs/props are used/created by signatures and documents, as well as full_needed needed to globally verify terms have a certain type/knowns are known **)

let adj x l = if List.mem x l then l else x::l

let rec signaspec_uses_objs_aux (dl:signaspec) r : (hashval * hashval) list =
  match dl with
  | SignaParam(h,a)::dr -> signaspec_uses_objs_aux dr (adj (h,hashtp a) r)
  | _::dr -> signaspec_uses_objs_aux dr r
  | [] -> r

let signaspec_uses_objs (dl:signaspec) : (hashval * hashval) list = signaspec_uses_objs_aux dl []

let rec signaspec_uses_props_aux (dl:signaspec) r : hashval list =
  match dl with
  | SignaKnown(p)::dr -> signaspec_uses_props_aux dr (adj (tm_hashroot p) r)
  | _::dr -> signaspec_uses_props_aux dr r
  | [] -> r

let signaspec_uses_props (dl:signaspec) : hashval list = signaspec_uses_props_aux dl []

let rec doc_uses_objs_aux (dl:doc) r : (hashval * hashval) list =
  match dl with
  | DocParam(h,a)::dr -> doc_uses_objs_aux dr (adj (h,hashtp a) r)
  | _::dr -> doc_uses_objs_aux dr r
  | [] -> r

let doc_uses_objs (dl:doc) : (hashval * hashval) list = doc_uses_objs_aux dl []

let rec doc_uses_props_aux (dl:doc) r : hashval list =
  match dl with
  | DocKnown(p)::dr -> doc_uses_props_aux dr (adj (tm_hashroot p) r)
  | _::dr -> doc_uses_props_aux dr r
  | [] -> r

let doc_uses_props (dl:doc) : hashval list = doc_uses_props_aux dl []

let rec doc_creates_objs_aux (dl:doc) r : (hashval * hashval) list =
  match dl with
  | DocDef(a,m)::dr -> doc_creates_objs_aux dr (adj (tm_hashroot m,hashtp a) r)
  | _::dr -> doc_creates_objs_aux dr r
  | [] -> r

let doc_creates_objs (dl:doc) : (hashval * hashval) list = doc_creates_objs_aux dl []

let rec doc_creates_props_aux (dl:doc) r : hashval list =
  match dl with
  | DocPfOf(p,d)::dr -> doc_creates_props_aux dr (adj (tm_hashroot p) r)
  | _::dr -> doc_creates_props_aux dr r
  | [] -> r

let doc_creates_props (dl:doc) : hashval list = doc_creates_props_aux dl []

let falsehashprop = tm_hashroot (All(Prop,DB(0)))
let neghashprop = tm_hashroot (Lam(Prop,Imp(DB(0),TmH(falsehashprop))))

let invert_neg_prop p =
  match p with
  | Imp(np,f) when tm_hashroot f = falsehashprop -> np
  | Ap(n,np) when tm_hashroot n = neghashprop -> np
  | _ -> raise Not_found

let rec doc_creates_neg_props_aux (dl:doc) r : hashval list =
  match dl with
  | DocPfOf(p,d)::dr ->
      begin
	try
	  let np = invert_neg_prop p in
	  doc_creates_neg_props_aux dr (adj (tm_hashroot np) r)
	with Not_found -> doc_creates_neg_props_aux dr r
      end
  | _::dr -> doc_creates_neg_props_aux dr r
  | [] -> r

let doc_creates_neg_props (dl:doc) : hashval list = doc_creates_neg_props_aux dl []

(** * htrees to hold theories and signatures **)
type ttree = theory htree
type stree = signa htree

let ottree_insert t bl thy =
  match t with
  | Some(t) -> htree_insert t bl thy
  | None -> htree_create bl thy

let ostree_insert t bl s =
  match t with
  | Some(t) -> htree_insert t bl s
  | None -> htree_create bl s

let ottree_hashroot t = ohtree_hashroot hashtheory 160 t

let ostree_hashroot t = ohtree_hashroot (fun s -> Some(hashsigna s)) 160 t

let ottree_lookup t h =
  match t,h with
  | Some(t),Some(h) ->
      begin
	match htree_lookup (hashval_bitseq h) t with
	| None -> raise Not_found
	| Some(thy) -> thy
      end
  | _,None -> ([],[])
  | _,_ -> raise Not_found

(** * operations including type checking and proof checking ***)

let beta_count = ref 200000
let term_count = ref 10000000

let reset_resource_limits () =
  beta_count := 200000;
  term_count := 10000000

exception BetaLimit
exception TermLimit

let beta_count_check () =
  if !beta_count > 0 then
    decr beta_count
  else
    raise BetaLimit

let term_count_check () =
  if !term_count > 0 then
    decr term_count
  else
    raise TermLimit

let rec tpshift i j a =
  term_count_check ();
  match a with
  | TpVar(k) when k < i -> TpVar(k)
  | TpVar(k) -> TpVar(k+j)
  | Ar(a1,a2) -> Ar(tpshift i j a1,tpshift i j a2)
  | TpAll(a) -> TpAll(tpshift (i+1) j a)
  | _ -> a

let rec tmtpshift i j m =
  term_count_check ();
  match m with
  | Ap(m1,m2) -> Ap(tmtpshift i j m1,tmtpshift i j m2)
  | Lam(a1,m1) -> Lam(tpshift i j a1,tmtpshift i j m1)
  | Imp(m1,m2) -> Imp(tmtpshift i j m1,tmtpshift i j m2)
  | All(a1,m1) -> All(tpshift i j a1,tmtpshift i j m1)
  | TTpAp(m1,a1) -> TTpAp(tmtpshift i j m1,tpshift i j a1)
  | TTpLam(m1) -> TTpLam(tmtpshift (i+1) j m1)
  | TTpAll(m1) -> TTpAll(tmtpshift (i+1) j m1)
  | _ -> m

(*** The shift and substitution operations are only valid if TmH only abbreviates
 closed terms (terms with no DBs and no TpVars).
 ***)
let rec tmshift i j m =
  term_count_check ();
  match m with
  | DB(k) when k < i -> DB(k)
  | DB(k) -> DB(k+j)
  | Ap(m1,m2) -> Ap(tmshift i j m1,tmshift i j m2)
  | Lam(a1,m1) -> Lam(a1,tmshift (i+1) j m1)
  | Imp(m1,m2) -> Imp(tmshift i j m1,tmshift i j m2)
  | All(a1,m1) -> All(a1,tmshift (i+1) j m1)
  | TTpAp(m1,a1) -> TTpAp(tmshift i j m1,a1)
  | TTpLam(m1) -> TTpLam(tmshift i j m1)
  | TTpAll(m1) -> TTpAll(tmshift i j m1)
  | _ -> m

let rec tpsubst a j b =
  term_count_check ();
  match a with
  | TpVar(i) when i = j && j = 0 -> b
  | TpVar(i) when i = j -> tpshift 0 j b
  | TpVar(i) when i > j -> TpVar(i-1)
  | Ar(a1,a2) -> Ar(tpsubst a1 j b,tpsubst a2 j b)
  | TpAll(a1) -> TpAll(tpsubst a1 (j+1) b)
  | _ -> a

let rec tmtpsubst m j b =
  term_count_check ();
  match m with
  | Ap(m1,m2) -> Ap(tmtpsubst m1 j b,tmtpsubst m2 j b)
  | Lam(a1,m1) -> Lam(tpsubst a1 j b,tmtpsubst m1 j b)
  | Imp(m1,m2) -> Imp(tmtpsubst m1 j b,tmtpsubst m2 j b)
  | All(a1,m1) -> All(tpsubst a1 j b,tmtpsubst m1 j b)
  | TTpAp(m,a) -> TTpAp(tmtpsubst m j b,tpsubst a j b)
  | TTpLam(m) -> TTpLam(tmtpsubst m (j+1) b)
  | TTpAll(m) -> TTpAll(tmtpsubst m (j+1) b)
  | _ -> m

let rec tmsubst m j n =
  term_count_check ();
  match m with
  | DB(i) when i = j && j = 0 -> n
  | DB(i) when i = j -> tmshift 0 j n
  | DB(i) when i > j -> DB(i-1)
  | Ap(m1,m2) -> Ap(tmsubst m1 j n,tmsubst m2 j n)
  | Lam(a,m1) -> Lam(a,tmsubst m1 (j+1) n)
  | Imp(m1,m2) -> Imp(tmsubst m1 j n,tmsubst m2 j n)
  | All(a,m1) -> All(a,tmsubst m1 (j+1) n)
  | _ -> m

let rec free_tpvar_in_tp_p a j =
  match a with
  | TpVar(i) when i = j -> true
  | Ar(a1,a2) -> free_tpvar_in_tp_p a1 j || free_tpvar_in_tp_p a2 j
  | TpAll(a) -> free_tpvar_in_tp_p a (j+1)
  | _ -> false

let rec free_tpvar_in_tm_p m j =
  match m with
  | Ap(m1,m2) -> free_tpvar_in_tm_p m1 j || free_tpvar_in_tm_p m2 j
  | Lam(a,m1) -> free_tpvar_in_tp_p a j || free_tpvar_in_tm_p m1 j
  | Imp(m1,m2) -> free_tpvar_in_tm_p m1 j || free_tpvar_in_tm_p m2 j
  | All(a,m1) -> free_tpvar_in_tp_p a j || free_tpvar_in_tm_p m1 j
  | TTpAp(m1,a) -> free_tpvar_in_tm_p m1 j || free_tpvar_in_tp_p a j
  | TTpLam(m1) -> free_tpvar_in_tm_p m1 (j+1)
  | TTpAll(m1) -> free_tpvar_in_tm_p m1 (j+1)
  | _ -> false

let rec free_in_tm_p m j =
  match m with
  | DB(i) when i = j -> true
  | Ap(m1,m2) -> free_in_tm_p m1 j || free_in_tm_p m2 j
  | Lam(a,m1) -> free_in_tm_p m1 (j+1)
  | Imp(m1,m2) -> free_in_tm_p m1 j || free_in_tm_p m2 j
  | All(a,m1) -> free_in_tm_p m1 (j+1)
  | _ -> false

(** check if a term is beta eta normal (not delta; defns can appear) **)
let rec tm_norm_p m =
  match m with
  | Ap(Lam(_,_),_) -> false
  | TTpAp(TTpLam(_),_) -> false
  | Lam(a,Ap(f,DB(0))) when not (free_in_tm_p f 0) -> false
  | TTpLam(TTpAp(f,TpVar(0))) when not (free_tpvar_in_tm_p f 0) -> false
  | Ap(m1,m2) -> tm_norm_p m1 && tm_norm_p m2
  | Lam(a,m1) -> tm_norm_p m1
  | Imp(m1,m2) -> tm_norm_p m1 && tm_norm_p m2
  | All(a,m1) -> tm_norm_p m1
  | TTpAp(m1,a) -> tm_norm_p m1
  | TTpLam(m1) -> tm_norm_p m1
  | TTpAll(m1) -> tm_norm_p m1
  | _ -> true

let rec tm_beta_eta_norm_1 m =
  match m with
  | Ap(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_norm_1 m2 in
      begin
	match m1r with
	| Lam(a,m) ->
	    beta_count_check ();
	    (tmsubst m 0 m2r,false) (*** beta ***)
	| _ -> (Ap(m1r,m2r),m1b && m2b)
      end
  | Lam(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      begin
	match m1r with
	| Ap(m1f,DB(0)) when not (free_in_tm_p m1f 0) -> (tmshift 0 (-1) m1f,false) (*** eta ***)
	| _ -> (Lam(a,m1r),m1b)
      end
  | TTpAp(m1,a) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      begin
	match m1r with
	| TTpLam(m) ->
	    beta_count_check ();
	    (tmtpsubst m 0 a,false) (*** type level beta ***)
	| _ -> (TTpAp(m1r,a),m1b)
      end
  | TTpLam(m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      begin
	match m1r with
	| TTpAp(m1f,TpVar(0)) when not (free_tpvar_in_tm_p m1f 0) -> (tmtpshift 0 (-1) m1f,false) (*** type level eta ***)
	| _ -> (TTpLam(m1r),m1b)
      end
  | Imp(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_norm_1 m2 in
      (Imp(m1r,m2r),m1b && m2b)
  | All(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      (All(a,m1r),m1b)
  | TTpAll(m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      (TTpAll(m1r),m1b)
  | _ -> (m,true)

let rec tm_beta_eta_norm m =
  let (mr,mb) = tm_beta_eta_norm_1 m in
  if mb then
    mr
  else
    tm_beta_eta_norm mr

exception CheckingFailure
exception NotKnown of hashval option * hashval
exception UnknownTerm of hashval option * hashval * tp
exception UnknownSigna of hashval

let tp_of_prim thy i =
  match thy with
  | (tpl,_) ->
      try
	List.nth tpl i
      with Failure "nth" -> raise CheckingFailure

let rec tp_of_tmh_r tpl h =
  match tpl with
  | [] -> raise Not_found
  | (k,a,_)::_ when h = k -> a
  | _::tpr -> tp_of_tmh_r tpr h

let tp_of_tmh sg h =
  match sg with
  | (tpl,_) -> tp_of_tmh_r tpl h

let rec def_of_tmh_r tpl h =
  match tpl with
  | [] -> raise Not_found
  | (k,_,om)::_ when h = k ->
      begin
	match om with
	| Some(m) -> m
	| None -> raise Not_found
      end
  | _::tpr -> def_of_tmh_r tpr h

let def_of_tmh sg h =
  match sg with
  | (tpl,_) -> def_of_tmh_r tpl h

let rec prop_of_known_r kl h =
  match kl with
  | (k,p)::_ when h = k -> p
  | _::kr -> prop_of_known_r kr h
  | [] -> raise Not_found 

let prop_of_known sg h =
  match sg with
  | (_,kl) ->
      prop_of_known_r kl h

exception NonNormalTerm

let rec check_tp v a =
  match a with
  | TpVar(x) when x >= v -> raise CheckingFailure
  | Ar(a1,a2) -> (check_tp v a1; check_tp v a2)
  | TpAll(a1) -> raise CheckingFailure
  | _ -> ()

let rec check_ptp v a =
  match a with
  | TpAll(a1) -> check_ptp (v+1) a1
  | _ -> check_tp v a

let rec extr_tpoftm thy sg v cxtm m =
  match m with
  | DB i ->
      begin
	try
	  List.nth cxtm i
	with Failure "nth" -> raise CheckingFailure
      end
  | Prim(i) ->
      begin
	try
	  tp_of_prim thy i
	with Not_found -> raise CheckingFailure
      end
  | TmH h ->
      begin
	try
	  tp_of_tmh sg h
	with Not_found -> raise CheckingFailure
      end
  | Ap(m1,m2) ->
      begin
	match extr_tpoftm thy sg v cxtm m1 with
	| Ar(a,b) -> (check_tpoftm thy sg v cxtm m2 a; b)
	| _ -> raise CheckingFailure
      end
  | TTpAp(m1,a) ->
      begin
	check_tp v a;
	match extr_tpoftm thy sg v cxtm m1 with
	| TpAll(b) -> tpsubst b 0 a
	| _ -> raise CheckingFailure
      end
  | Lam(a,m) -> (check_tp v a; Ar(a,extr_tpoftm thy sg v (a::cxtm) m))
  | TTpLam(m) -> TpAll(extr_tpoftm thy sg (v+1) (List.map (tpshift 0 1) cxtm) m)
  | Imp(m1,m2) -> (check_tpoftm thy sg v cxtm m1 Prop; check_tpoftm thy sg v cxtm m2 Prop; Prop)
  | All(a,m) -> (check_tp v a; check_tpoftm thy sg v (a::cxtm) m Prop; Prop)
  | TTpAll(_) -> raise CheckingFailure
and check_tpoftm thy sg v cxtm m a =
  let b = extr_tpoftm thy sg v cxtm m in
  if a = b then
    ()
  else
    raise CheckingFailure

let rec check_metaprop thy sg v m =
  match m with
  | TTpAll(m) -> check_metaprop thy sg (v+1) m
  | _ -> check_tpoftm thy sg v [] m Prop

let rec tm_head_args_r2 m tpargs args =
  match m with
  | TTpAp(m1,a2) -> tm_head_args_r2 m1 (a2::tpargs) args
  | _ -> (m,tpargs,args)

let rec tm_head_args_r m args =
  match m with
  | Ap(m1,m2) -> tm_head_args_r m1 (m2::args)
  | TTpAp(m1,a2) -> tm_head_args_r2 m1 [a2] args
  | _ -> (m,[],args)

let tm_head_args m =
  tm_head_args_r m []

(*** assume m is beta eta normal and not a Lam, and args are all beta eta normal ***)
let rec tm_app_beta_eta_norm3 m args =
  match args with
  | (n::argr) -> tm_app_beta_eta_norm3 (Ap(m,n)) argr
  | _ -> m

let rec tm_app_beta_eta_norm2 m tpargs args =
  match tpargs with
  | (a::tpargr) -> tm_app_beta_eta_norm2 (TTpAp(m,a)) tpargr args
  | _ -> tm_app_beta_eta_norm3 m args

(*** assume m is beta eta normal already and args are all beta eta normal ***)
let rec tm_app_beta_eta_norm m tpargs args =
  match (m,tpargs,args) with
  | (TTpLam(m1),a::tpargr,args) ->
      tm_app_beta_eta_norm (tm_beta_eta_norm (tmtpsubst m1 0 a)) tpargr args
  | (Lam(_,m1),[],n::argr) ->
      tm_app_beta_eta_norm (tm_beta_eta_norm (tmsubst m1 0 n)) [] argr
  | _ ->
      tm_app_beta_eta_norm2 m tpargs args

(*** assume all defs are beta eta normal ***)
let delta_exp sg h args =
  match h with
  | TmH(c) ->
      let m = def_of_tmh sg c in
      tm_app_beta_eta_norm m args
  | _ -> raise Not_found

let deltap dl h =
  match h with
  | TmH(c) -> List.mem c dl
  | _ -> false

let delta_cons h dl =
  match h with
  | TmH(c) -> if List.mem c dl then dl else (c::dl)
  | _ -> dl

let rec headnorm1 sg m dl =
  match m with
  | TTpAll(_) -> (m,dl)
  | TTpLam(_) -> (m,dl)
  | Lam(_,_) -> (m,dl)
  | Imp(_,_) -> (m,dl)
  | All(_,_) -> (m,dl)
  | _ ->
      let (mh,mtpargs,margs) = tm_head_args m in
      try
	let m2 = delta_exp sg mh mtpargs margs in
	headnorm1 sg m2 (delta_cons mh dl)
      with Not_found ->
	(m,dl)

let headnorm sg m dl = headnorm1 sg (tm_beta_eta_norm m) dl

(*** conv2 assumes m and n are beta-eta normal ***)
let rec conv2 m n sg dl =
  match (m,n) with
  | (Lam(a1,m1),Lam(b1,n1)) ->
      if a1 = b1 then
	conv2 m1 n1 sg dl
      else
	None
  | (All(a1,m1),All(b1,n1)) ->
      if a1 = b1 then
	conv2 m1 n1 sg dl
      else
	None
  | (Imp(m1,m2),Imp(n1,n2)) ->
      convl [m1;m2] [n1;n2] sg dl
  | (TTpLam(m1),TTpLam(n1)) ->
      conv2 m1 n1 sg dl
  | (TTpAll(m1),TTpAll(n1)) ->
      conv2 m1 n1 sg dl
  | (Lam(_,_),All(_,_)) -> None
  | (Lam(_,_),Imp(_,_)) -> None
  | (Lam(_,_),TTpAll(_)) -> None
  | (Lam(_,_),TTpLam(_)) -> None
  | (All(_,_),Lam(_,_)) -> None
  | (All(_,_),Imp(_,_)) -> None
  | (All(_,_),TTpAll(_)) -> None
  | (All(_,_),TTpLam(_)) -> None
  | (Imp(_,_),All(_,_)) -> None
  | (Imp(_,_),Lam(_,_)) -> None
  | (Imp(_,_),TTpAll(_)) -> None
  | (Imp(_,_),TTpLam(_)) -> None
  | (TTpAll(_),Lam(_,_)) -> None
  | (TTpAll(_),All(_,_)) -> None
  | (TTpAll(_),Imp(_,_)) -> None
  | (TTpAll(_),TTpLam(_)) -> None
  | (TTpLam(_),Lam(_,_)) -> None
  | (TTpLam(_),All(_,_)) -> None
  | (TTpLam(_),Imp(_,_)) -> None
  | (TTpLam(_),TTpAll(_)) -> None
  | (_,Lam(_,_)) ->
      let (mh,mtpargs,margs) = tm_head_args m in
      begin
	try
	  conv2 (delta_exp sg mh mtpargs margs) n sg (delta_cons mh dl)
	with Not_found -> None
      end
  | (_,All(_,_)) ->
      let (mh,mtpargs,margs) = tm_head_args m in
      begin
	try
	  conv2 (delta_exp sg mh mtpargs margs) n sg (delta_cons mh dl)
	with Not_found -> None
      end
  | (_,Imp(_,_)) ->
      let (mh,mtpargs,margs) = tm_head_args m in
      begin
	try
	  conv2 (delta_exp sg mh mtpargs margs) n sg (delta_cons mh dl)
	with Not_found -> None
      end
  | (Lam(_,_),_) ->
      let (nh,ntpargs,nargs) = tm_head_args n in
      begin
	try
	  conv2 m (delta_exp sg nh ntpargs nargs) sg (delta_cons nh dl)
	with Not_found -> None
      end
  | (All(_,_),_) ->
      let (nh,ntpargs,nargs) = tm_head_args n in
      begin
	try
	  conv2 m (delta_exp sg nh ntpargs nargs) sg (delta_cons nh dl)
	with Not_found -> None
      end
  | (Imp(_,_),_) ->
      let (nh,ntpargs,nargs) = tm_head_args n in
      begin
	try
	  conv2 m (delta_exp sg nh ntpargs nargs) sg (delta_cons nh dl)
	with Not_found -> None
      end
  | (_,TTpAll(_)) ->
      let (mh,mtpargs,margs) = tm_head_args m in
      begin
	try
	  conv2 (delta_exp sg mh mtpargs margs) n sg (delta_cons mh dl)
	with Not_found -> None
      end
  | (_,TTpLam(_)) ->
      let (mh,mtpargs,margs) = tm_head_args m in
      begin
	try
	  conv2 (delta_exp sg mh mtpargs margs) n sg (delta_cons mh dl)
	with Not_found -> None
      end
  | (TTpAll(_),_) ->
      let (nh,ntpargs,nargs) = tm_head_args n in
      begin
	try
	  conv2 m (delta_exp sg nh ntpargs nargs) sg (delta_cons nh dl)
	with Not_found -> None
      end
  | (TTpLam(_),_) ->
      let (nh,ntpargs,nargs) = tm_head_args n in
      begin
	try
	  conv2 m (delta_exp sg nh ntpargs nargs) sg (delta_cons nh dl)
	with Not_found -> None
      end
  | _ ->
      let (mh,mtpargs,margs) = tm_head_args m in
      begin
	try
	  if deltap dl mh then
	    conv2 (delta_exp sg mh mtpargs margs) n sg dl
	  else
	    begin
	      match convrigid1 mh mtpargs margs n sg dl with
	      | Some(dl) -> Some(dl)
	      | None -> (*** try delta expanding mh ***)
		  conv2 (delta_exp sg mh mtpargs margs) n sg (delta_cons mh dl)
	    end
	with Not_found -> convrigid1 mh mtpargs margs n sg dl
      end
and convrigid1 mh mtpargs margs n sg dl =
  let (nh,ntpargs,nargs) = tm_head_args n in
  begin
    try
      if deltap dl nh then
	convrigid1 mh mtpargs margs (delta_exp sg nh ntpargs nargs) sg dl
      else
	begin
	  match convrigid2 mh mtpargs margs nh ntpargs nargs sg dl with
	  | Some(dl) -> Some(dl)
	  | None -> (*** try delta expanding nh ***)
	      convrigid1 mh mtpargs margs (delta_exp sg nh ntpargs nargs) sg (delta_cons nh dl)
	end
    with Not_found -> convrigid2 mh mtpargs margs nh ntpargs nargs sg dl
  end
and convrigid2 mh mtpargs margs nh ntpargs nargs sg dl =
  if mh = nh && mtpargs = ntpargs then
    convl margs nargs sg dl
  else
    None
and convl ml nl sg dl =
  match (ml,nl) with
  | ([],[]) -> Some(dl)
  | (m::mr,n::nr) ->
      begin
	match conv2 m n sg dl with
	| Some(dl) -> convl mr nr sg dl
	| None -> None
      end
  | _ -> None

let conv m n sg dl =
  conv2 (tm_beta_eta_norm m) (tm_beta_eta_norm n) sg dl

let rec extr_propofpf (thy:theory) sg v cxtm cxpf d dl =
  match d with
  | Hyp j ->
      begin
	try
	  (List.nth cxpf j,dl)
	with Failure "nth" -> raise CheckingFailure
      end
  | Known(h) ->
      begin
	try
	  let p = prop_of_known sg h in
	  (p,dl)
	with Not_found ->
	  raise CheckingFailure
      end
  | PTmAp(d1,m) ->
      begin
	let (q,dl) = extr_propofpf thy sg v cxtm cxpf d1 dl in
	match headnorm sg q dl with
	| (All(a,p),dl) ->
	    if extr_tpoftm thy sg v cxtm m = a then
	      (tmsubst p 0 m,dl)
	    else
	      raise CheckingFailure
	| _ ->
	    raise CheckingFailure
      end
  | PPfAp(d1,d2) ->
      begin
	let (q,dl) = extr_propofpf thy sg v cxtm cxpf d1 dl in
	match headnorm sg q dl with
	| (Imp(p1,p2),dl) ->
	    let dl = check_propofpf thy sg v cxtm cxpf d2 p1 dl in
	    (p2,dl)
	| _ ->
	    raise CheckingFailure
      end
  | TLam(a,d1) ->
      let (q,dl) = extr_propofpf thy sg v (a::cxtm) (List.map (fun q -> tmshift 0 1 q) cxpf) d1 dl in
      (All(a,q),dl)
  | PLam(p,d1) ->
      let (q,dl) = extr_propofpf thy sg v cxtm (p::cxpf) d1 dl in
      (Imp(p,q),dl)
  | PTpAp(d1,a) ->
      begin
	let (q,dl) = extr_propofpf thy sg v cxtm cxpf d1 dl in
	match headnorm sg q dl with
	| (TTpAll(p),dl) -> (tmtpsubst p 0 a,dl)
	| _ ->
	    raise CheckingFailure
      end
  | PTpLam(d1) ->
      let (q,dl) = extr_propofpf thy sg (v+1) cxtm cxpf d1 dl in
      (TTpAll(q),dl)
  | _ -> raise (Failure("Ill-formed Proof Term"))
and check_propofpf (thy:theory) sg v cxtm cxpf d p dl =
  let (q,dl) = extr_propofpf thy sg v cxtm cxpf d dl in
  match conv q p sg dl with
  | Some(dl) -> dl
  | None -> raise CheckingFailure

(*** return a theory and a gsigna or raise CheckingFailure ***)
let rec check_theoryspec dl : theory * gsigna  =
  match dl with
  | (ThyPrim(a)::dr) ->
      let ((tpl,kl1),gs) = check_theoryspec dr in
      check_ptp 0 a;
      ((tpl @ [a],kl1),gs)
  | (ThyDef(a,m)::dr) ->
      let (thy,(defl,kl)) = check_theoryspec dr in
      if not (tm_norm_p m) then raise NonNormalTerm;
      check_ptp 0 a;
      check_tpoftm thy (defl,kl) 0 [] m a;
      let h = tm_hashroot m in
      (thy,((h,a,Some(m))::defl,kl))
  | (ThyAxiom(p)::dr) ->
      let ((tpl,kl1),(defl,kl2)) = check_theoryspec dr in
      if not (tm_norm_p p) then raise NonNormalTerm;
      check_metaprop (tpl,kl1) (defl,kl2) 0 p; (*** check it in the theory with the prims so far and corresponding signature so far ***)
      let k = tm_hashroot p in
      ((tpl,k::kl1),(defl,(k,p)::kl2))
  | [] -> (([],[]),([],[]))

let rec import_signatures th (str:stree) hl sg imported =
  match hl with
  | [] -> (sg,imported)
  | (h::hr) ->
      if List.mem h imported then
	import_signatures th str hr sg imported
      else
	match htree_lookup (hashval_bitseq (hashopair2 th h)) str with (*** the theory is committed to only at the last moment ***)
	| Some(sl,(tptml2,kl2)) ->
	    let ((tptml3,kl3),imported) = import_signatures th str sl sg imported in
	    ((tptml3 @ tptml2,kl3 @ kl2),imported)
	| None ->
	    raise (UnknownSigna(h))

let tm_tp_p gvtp sg th h a =
  try
    let b = tp_of_tmh sg h in
    b = a
  with Not_found -> gvtp th h a

let known_p gvkn sg th k =
  try
    let _ = prop_of_known sg k in
    true
  with Not_found -> gvkn th k

(*** return the gsigna or raise CheckingFailure ***)
let rec check_signaspec_rec gvtp gvkn th thy (str:stree option) dl : gsigna * hashval list =
  match dl with
  | SignaSigna(h)::dr ->
      begin
	let (sg,imported) = check_signaspec_rec gvtp gvkn th thy str dr in
	match str with
	| Some(str) -> import_signatures th str [h] sg imported
	| None -> raise (UnknownSigna(h))
      end
  | SignaParam(h,a)::dr ->
      let ((tmtpl,kl),imported) = check_signaspec_rec gvtp gvkn th thy str dr in
      check_ptp 0 a;
      if tm_tp_p gvtp (tmtpl,kl) th h a then
	(((h,a,None)::tmtpl,kl),imported)
      else
	raise (UnknownTerm(th,h,a))
  | SignaDef(a,m)::dr ->
      let ((tmtpl,kl),imported) = check_signaspec_rec gvtp gvkn th thy str dr in
      if not (tm_norm_p m) then raise NonNormalTerm;
      check_ptp 0 a;
      check_tpoftm thy (tmtpl,kl) 0 [] m a;
      let h = tm_hashroot m in
      (((h,a,Some(m))::tmtpl,kl),imported)
  | SignaKnown(p)::dr ->
      let ((tmtpl,kl),imported) = check_signaspec_rec gvtp gvkn th thy str dr in
      if not (tm_norm_p p) then raise NonNormalTerm;
      check_metaprop thy (tmtpl,kl) 0 p;
      let k = tm_hashroot p in
      begin
	match thy with
	| (_,akl) ->
	    if List.mem k akl then (*** check if its the hash of an axiom ***)
	      ((tmtpl,(k,p)::kl),imported)
	    else if known_p gvkn (tmtpl,kl) th k then (*** check if it's either in the signature or globally known ***)
	      ((tmtpl,(k,p)::kl),imported)
	    else
	      raise (NotKnown(th,k)) (*** otherwise it cannot be declared as a known ***)
      end
  | [] -> (([],[]),[])

let check_signaspec gvtp gvkn th thy (str:stree option) dl : gsigna =
  reset_resource_limits();
  let (sg,_) = check_signaspec_rec gvtp gvkn th thy (str:stree option) dl in
  sg

(*** return gsigna (summarizing the document as a signature) or raise CheckingFailure ***)
let rec check_doc_rec gvtp gvkn th (thy:theory) (str:stree option) dl =
  match dl with
  | DocSigna(h)::dr ->
      begin
	let (sg,imported) = check_doc_rec gvtp gvkn th thy str dr in
	match str with
	| Some(str) -> import_signatures th str [h] sg imported
	| None -> raise (UnknownSigna(h))
      end
  | DocParam(h,a)::dr ->
      let ((tmtpl,kl),imported) = check_doc_rec gvtp gvkn th thy str dr in
      check_ptp 0 a;
      if tm_tp_p gvtp (tmtpl,kl) th h a then
	(((h,a,None)::tmtpl,kl),imported)
      else
	raise (UnknownTerm(th,h,a))
  | DocDef(a,m)::dr ->
      let ((tmtpl,kl),imported) = check_doc_rec gvtp gvkn th thy str dr in
      if not (tm_norm_p m) then raise NonNormalTerm;
      check_ptp 0 a;
      check_tpoftm thy (tmtpl,kl) 0 [] m a;
      let h = tm_hashroot m in
      (((h,a,Some(m))::tmtpl,kl),imported)
  | DocKnown(p)::dr ->
      let ((tmtpl,kl),imported) = check_doc_rec gvtp gvkn th thy str dr in
      if not (tm_norm_p p) then raise NonNormalTerm;
      check_metaprop thy (tmtpl,kl) 0 p;
      let k = tm_hashroot p in
      begin
	match thy with
	| (_,akl) ->
	    if List.mem k akl then (*** check if its the hash of an axiom ***)
	      ((tmtpl,(k,p)::kl),imported)
	    else if known_p gvkn (tmtpl,kl) th k then (*** check if it's either in the signature or globally known ***)
	      ((tmtpl,(k,p)::kl),imported)
	    else
	      raise (NotKnown(th,k)) (*** otherwise it cannot be declared as a known ***)
      end
  | DocConj(p)::dr ->
      let ((tmtpl,kl),imported) = check_doc_rec gvtp gvkn th thy str dr in
      if not (tm_norm_p p) then raise NonNormalTerm;
      check_metaprop thy (tmtpl,kl) 0 p;
      (*** We do not check that the conjecture really hasn't yet been proven. ***)
      (*** Note also that conjectures are not put onto the signature. This means a conjecture cannot be used in the rest of the document. ***)
      ((tmtpl,kl),imported)
  | DocPfOf(p,d)::dr ->
      let ((tmtpl,kl),imported) = check_doc_rec gvtp gvkn th thy str dr in
      if not (tm_norm_p p) then raise NonNormalTerm;
      check_metaprop thy (tmtpl,kl) 0 p;
      let _ = check_propofpf thy (tmtpl,kl) 0 [] [] d p [] in (** returns list of defns expanded, but not currently using it **)
      let k = tm_hashroot p in
      ((tmtpl,(k,p)::kl),imported)
  | [] -> (([],[]),[])

let rec check_doc gvtp gvkn th (thy:theory) (str:stree option) dl =
  reset_resource_limits();
  let (sg,_) = check_doc_rec gvtp gvkn th (thy:theory) (str:stree option) dl in
  sg
