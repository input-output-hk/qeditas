Require Export Docs.
Require Export DocHash.
Require Export Tree.
Require Export MathData.

Definition gvtpT := option hashval -> hashval -> stp -> bool.
Definition gvknT := option hashval -> hashval -> bool.

Inductive crt_theoryspec : theoryspec -> theory -> gsign -> Prop :=
| thy_nil : crt_theoryspec nil (nil, nil) (nil, nil)
| thy_prim : forall (spec : theoryspec) (thy : theory) (sgn : gsign) (a : stp) (thy0 : theory),
  crt_theoryspec spec thy sgn ->
  crt_stp 0 false (Z.of_nat (length (fst thy))) a ->
  thy0 = (fst thy ++ a::nil, snd thy) ->
  crt_theoryspec (thyprim a :: spec) thy0 sgn
| thy_def : forall (spec : theoryspec) (thy : theory) (sgn : gsign) (a : stp) (m : trm),
  crt_theoryspec spec thy sgn ->
  crt_stp 0 false (Z.of_nat (length (fst thy))) a ->
  crt_trm 0 true nil sgn (fst thy) m a ->
  is_norm m = true ->
  crt_theoryspec (thydef a m::spec) thy ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn)

| thy_axiom : forall (spec : theoryspec) (thy : theory) (sgn : gsign) (p : trm),
  crt_theoryspec spec thy sgn ->
  crt_trm 0 false nil sgn (fst thy) p prop ->
  is_norm p = true ->
  crt_theoryspec (thyaxiom p::spec) (fst thy, trm_hashroot p::snd thy) (fst sgn, (trm_hashroot p, p)::snd sgn).

Axiom thy_nil_rev :  forall (t : theory) (sgn : gsign), crt_theoryspec nil t sgn -> t = (nil, nil) /\ sgn = (nil, nil).
Axiom thy_prim_rev : forall (spec : theoryspec) (a : stp) (thy0 : theory) (sgn : gsign),
  crt_theoryspec (thyprim a :: spec) thy0 sgn ->
  exists (thy : theory),
    crt_stp 0 false (Z.of_nat (length (fst thy))) a /\
    thy0 = (fst thy ++ a::nil, snd thy) /\
    crt_theoryspec spec thy sgn.
Axiom thy_def_rev : forall (spec : theoryspec) (thy : theory) (sgn0 : gsign) (a : stp) (m : trm) ,
  crt_theoryspec (thydef a m :: spec) thy sgn0 -> 
  exists (sgn : gsign),
    sgn0 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn) /\
    crt_theoryspec spec thy sgn /\
    crt_stp 0 false (Z.of_nat (length (fst thy))) a /\
    crt_trm 0 true nil sgn (fst thy) m a /\
    is_norm m = true.
Axiom thy_axiom_rev : forall (spec : theoryspec) (thy0 : theory) (sgn0 : gsign) (p : trm),
  crt_theoryspec (thyaxiom p :: spec) thy0 sgn0 ->
  exists (thy : theory) (sgn : gsign),
    thy0 = (fst thy, trm_hashroot p::snd thy) /\
    sgn0 = (fst sgn, (trm_hashroot p, p)::snd sgn) /\
    crt_theoryspec spec thy sgn /\
    crt_trm 0 false nil sgn (fst thy) p prop /\
    is_norm p = true.

Inductive crt_signaspec : gvtpT -> gvknT -> option stree -> option hashval -> theory -> signaspec -> gsign -> list hashval -> Prop :=
| sgn_nil : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option (stree)) (th:option hashval) (thy:theory),
crt_signaspec gvtp gvkn st th thy nil (nil, nil) nil
| sgn_signa : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option (stree)) (th:option hashval) (thy:theory) (s:signaspec) (sgn : gsign) (imp : list hashval) (sgn2 : gsign) (imp2 : list hashval) (h : hashval) (str : stree),
  crt_signaspec gvtp gvkn st th thy s sgn imp ->
  st = Some str ->
  Some (sgn2, imp2) = import_signatures th str (h::nil) sgn imp ->
  crt_signaspec gvtp gvkn st th thy (signasigna h:: s) sgn2 imp2
| sgn_param : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option (stree)) (th:option hashval) (thy:theory) (s:signaspec) (sgn : gsign) (sgn2 : gsign) (imp : list hashval) (h : hashval) (a : stp),
  crt_signaspec gvtp gvkn st th thy s sgn imp ->
  crt_stp 0 false (Z.of_nat (length (fst thy))) a ->
  tm_tp gvtp sgn th h a = true ->
  ((h, a, None)::fst sgn, snd sgn) = sgn2 ->
  crt_signaspec gvtp gvkn st th thy (signaparam h a ::s) sgn2 imp
| sgn_def : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option (stree)) (th:option hashval) (thy:theory) (s:signaspec) (sgn : gsign) (sgn2 : gsign) (imp : list hashval) (a : stp) (m : trm),
  crt_signaspec gvtp gvkn st th thy s sgn imp ->
  is_norm m = true ->
  crt_stp 0 false (Z.of_nat (length (fst thy))) a ->
  crt_trm 0 true nil sgn (fst thy) m a ->
  ((exists h, m = TmH h) -> sgn2 = sgn) ->
  ((~exists h, m = TmH h) -> sgn2 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn)) ->
  crt_signaspec gvtp gvkn st th thy (signadef a m :: s) sgn2 imp
| sgn_known : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option (stree)) (th:option hashval) (thy:theory) (s:signaspec) (sgn : gsign) (imp : list hashval) (p :trm),
  crt_signaspec gvtp gvkn st th thy s sgn imp ->
  is_norm p = true ->
  crt_trm 0 false nil sgn (fst thy) p prop ->
  (In (trm_hashroot p) (snd thy) \/ known gvkn sgn th (trm_hashroot p) = true) ->
  crt_signaspec gvtp gvkn st th thy (signaknown p :: s) (fst sgn, (trm_hashroot p, p)::snd sgn) imp.                


Axiom sgn_nil_rev : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option (stree)) (th:option hashval) (thy:theory) (sgn : gsign) (imp : list hashval),
crt_signaspec gvtp gvkn st th thy nil sgn imp -> sgn = (nil, nil) /\ imp = nil.

Axiom sgn_signa_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (h : hashval),
  crt_signaspec gvtp gvkn st th t (signasigna h::s) sgn2 imp2 ->
  exists (sgn : gsign) (imp : list hashval) (str : stree) ,
  crt_signaspec gvtp gvkn st th t s sgn imp /\
  st = Some str /\
  Some (sgn2, imp2) = import_signatures th str (h::nil) sgn imp.

Axiom sgn_param_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (h : hashval)(a : stp),
  crt_signaspec gvtp gvkn st th t (signaparam h a::s) sgn2 imp2 ->
  exists (sgn : gsign),
  crt_signaspec gvtp gvkn st th t s sgn imp2 /\
  tm_tp gvtp sgn th h a = true /\
  crt_stp 0 false (Z.of_nat (length (fst t))) a /\
  sgn2 = ((h, a, None)::fst sgn, snd sgn).

Axiom sgn_def_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (m : trm)(a : stp),
  crt_signaspec gvtp gvkn st th t (signadef a m::s) sgn2 imp2 ->
  exists (sgn : gsign),
  is_norm m = true /\
  crt_stp 0 false (Z.of_nat (length (fst t))) a /\
  crt_trm 0 true nil sgn (fst t) m a /\
  ((exists h, m = TmH h) -> sgn2 = sgn) /\ ( (~exists h, m = TmH h) -> sgn2 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn)) /\
  crt_signaspec gvtp gvkn st th t s sgn imp2.

Axiom sgn_known_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (p : trm),
  crt_signaspec gvtp gvkn st th t (signaknown p::s) sgn2 imp2 ->
  exists (sgn : gsign),
  crt_signaspec gvtp gvkn st th t s sgn imp2 /\
  is_norm p = true /\
  crt_trm 0 false nil sgn (fst t) p prop /\
  sgn2 = (fst sgn, (trm_hashroot p, p) :: snd sgn) /\
  (In (trm_hashroot p) (snd t) \/ known gvkn sgn th (trm_hashroot p) = true).
 
Inductive crt_doc :  gvtpT -> gvknT -> option stree -> option hashval -> theory -> doc -> gsign -> list hashval -> Prop :=
| doc_nil : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option stree) (th:option hashval) (thy:theory),
  crt_doc gvtp gvkn st th thy nil (nil, nil) nil
| doc_sign : forall (gvtp : gvtpT) (gvkn : gvknT)  (str : stree) (st:option stree) (th:option hashval) (thy:theory) (dl:doc) (sgn : gsign) (imp : list hashval) (sgn2 : gsign) (imp2 : list hashval) (h : hashval),
  crt_doc gvtp gvkn st th thy dl sgn imp ->
  st = Some str ->
  Some (sgn2, imp2) = import_signatures th str (h::nil) sgn imp ->
  crt_doc gvtp gvkn st th thy (docsigna h:: dl) sgn2 imp2
| doc_param : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option stree) (th:option hashval) (thy:theory) (dl:doc) (sgn : gsign) (imp : list hashval) (h : hashval) (a : stp),
  crt_doc gvtp gvkn st th thy dl sgn imp ->
  crt_stp 0 false (Z.of_nat (length (fst thy))) a ->
  tm_tp gvtp sgn th h a = true ->
  crt_doc gvtp gvkn st th thy (docparam h a ::dl) ((h, a, None)::fst sgn, snd sgn) imp

| doc_def : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option stree) (th:option hashval) (thy:theory) (dl:doc) (sgn : gsign) (sgn2 : gsign) (imp : list hashval) (a : stp) (m : trm),
  crt_doc gvtp gvkn st th thy dl sgn imp ->
  is_norm m = true ->
  crt_stp 0 false (Z.of_nat (length (fst thy))) a ->
  crt_trm 0 true nil sgn (fst thy) m a ->
  ((exists h, m = TmH h) -> sgn2 = sgn) ->
  ((~exists h, m = TmH h) -> sgn2 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn)) ->
  crt_doc gvtp gvkn st th thy (docdef a m ::dl) sgn2 imp

| doc_known : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option stree) (th:option hashval) (thy:theory) (dl:doc) (sgn : gsign) (imp : list hashval) (p : trm),
  crt_doc gvtp gvkn st th thy dl sgn imp ->
  is_norm p = true ->
  crt_trm 0 false nil sgn (fst thy) p prop ->
  (In (trm_hashroot p) (snd thy) \/ known gvkn sgn th (trm_hashroot p) = true) ->
  crt_doc gvtp gvkn st th thy (docknown p :: dl) (fst sgn, (trm_hashroot p, p)::snd sgn) imp
| doc_conj : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option stree) (th:option hashval) (thy:theory) (dl:doc) (sgn : gsign) (imp : list hashval) (p : trm),
  crt_doc gvtp gvkn st th thy dl sgn imp ->
  is_norm p = true ->
  crt_trm 0 false nil sgn (fst thy) p prop ->
  crt_doc gvtp gvkn st th thy (docconj p ::dl) sgn imp

| doc_pf : forall (gvtp : gvtpT) (gvkn : gvknT) (st:option stree) (th:option hashval) (thy:theory) (dl:doc) (sgn : gsign) (imp : list hashval) (d : pf) (p : trm) (p2 : trm),
  crt_doc gvtp gvkn st th thy dl sgn imp ->
  is_norm p = true ->
  crt_trm 0 false nil sgn (fst thy) p prop ->
  Some p2 = beta_eta_delta_norm p sgn ->
  crt_pf 0 nil nil sgn (fst thy) d p2 ->
  crt_doc gvtp gvkn st th thy (docpfof p d ::dl) (fst sgn, (trm_hashroot p, p) :: snd sgn) imp.


Axiom doc_nil_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (thy : theory)(sgn : gsign) (imp : list hashval),
  crt_doc gvtp gvkn st th thy nil sgn imp -> sgn = (nil, nil) /\ imp = nil.

Axiom doc_sign_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (h : hashval),
  crt_doc gvtp gvkn st th t (docsigna h:: d) sgn2 imp2 ->
  exists (sgn : gsign) (imp : list hashval) (str : stree) ,
  st = Some str /\
  crt_doc gvtp gvkn st th t d sgn imp /\
  Some (sgn2, imp2) = import_signatures th str (h::nil) sgn imp.

Axiom doc_param_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (h : hashval)(a : stp),
  crt_doc gvtp gvkn st th t (docparam h a ::d) sgn2 imp2 ->
  exists (sgn : gsign),
  crt_doc gvtp gvkn st th t d sgn imp2 /\
  tm_tp gvtp sgn th h a = true /\
  crt_stp 0 false (Z.of_nat (length (fst t))) a /\
  sgn2 = ((h, a, None)::fst sgn, snd sgn).

Axiom doc_def_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (m : trm)(a : stp),
  crt_doc gvtp gvkn st th t (docdef a m ::d) sgn2 imp2 ->
  exists (sgn : gsign),
  is_norm m = true /\
  crt_stp 0 false (Z.of_nat (length (fst t))) a /\
  crt_trm 0 true nil sgn (fst t) m a /\
  ((exists h, m = TmH h) -> sgn2 = sgn) /\ ( (~exists h, m = TmH h) -> sgn2 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn)) /\
  crt_doc gvtp gvkn st th t d sgn imp2.


Axiom doc_known_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (p : trm),
  crt_doc gvtp gvkn st th t (docknown p :: d) sgn2 imp2 ->
  exists (sgn : gsign),
  crt_doc gvtp gvkn st th t d sgn imp2 /\
  is_norm p = true /\
  crt_trm 0 false nil sgn (fst t) p prop /\
  sgn2 = (fst sgn, (trm_hashroot p, p) :: snd sgn) /\
  (In (trm_hashroot p) (snd t) \/ known gvkn sgn th (trm_hashroot p) = true).

Axiom doc_conj_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (p : trm),
  crt_doc gvtp gvkn st th t (docconj p ::d) sgn2 imp2 ->
  crt_doc gvtp gvkn st th t d sgn2 imp2 /\
  is_norm p = true /\
  crt_trm 0 false nil sgn2 (fst t) p prop.

Axiom doc_pfof_rev : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (p : trm) (e : pf),
  crt_doc gvtp gvkn st th t (docpfof p e ::d) sgn2 imp2 ->
  exists (sgn : gsign) (p2 : trm),
  crt_doc gvtp gvkn st th t d sgn imp2 /\
  sgn2 = (fst sgn, (trm_hashroot p, p) :: snd sgn) /\
  is_norm p = true /\
  Some p2 = beta_eta_delta_norm p sgn /\
  crt_pf 0 nil nil sgn (fst t) e p2 /\
  crt_trm 0 false nil sgn (fst t) p prop.


