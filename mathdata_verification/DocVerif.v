Require Export DocLogic.
Require Export ProofVerif.
Require Export SgnVerif.
Require Export MathData.
Require Import Bool Arith List Cpdt.CpdtTactics.

Lemma doc_sign_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (h : hashval),
  check_doc gvtp gvkn th t st (docsigna h :: d) = Some (sgn2, imp2) ->
  exists (sgn : gsign) (imp : list hashval) (str : stree) ,
  st = Some str /\
  check_doc gvtp gvkn th t st d = Some(sgn, imp) /\
  Some (sgn2, imp2) = import_signatures th str (h::nil) sgn imp.
Proof.
  intros.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct p.
  destruct st.
  exists g. exists l. exists s.
  split.
  reflexivity.
  split.
  reflexivity.
  rewrite H.
  reflexivity.
  discriminate.
  discriminate.
Qed.

Lemma doc_param_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (h : hashval)(a : stp),
  check_doc gvtp gvkn th t st (docparam h a::d) = Some (sgn2, imp2) ->
  exists (sgn : gsign),
  check_doc gvtp gvkn th t st d = Some(sgn, imp2) /\
  tm_tp gvtp sgn th h a = true /\
  correct_tp 0 a (Z.of_nat (length (fst t))) = true /\
  sgn2 = ((h, a, None)::fst sgn, snd sgn).
Proof.
  intros.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct p.
  exists g.
  destruct g.
  split.
  destruct (correct_tp 0 a (Z.of_nat (length (fst t)))).
  destruct (tm_tp gvtp (l0, l1) th h a).
  simpl in H.
  assert (l = imp2).
  crush.
  rewrite H0.
  reflexivity.
  discriminate.
  simpl in H.
  discriminate.
  split.

  destruct (correct_tp 0 a (Z.of_nat (length (fst t)))).
  destruct (tm_tp gvtp (l0, l1) th h a).
  reflexivity.
  simpl in H.
  discriminate.
  destruct (tm_tp gvtp (l0, l1) th h a).
  reflexivity.
  simpl in H.
  discriminate.

  destruct (correct_tp 0 a (Z.of_nat (length (fst t)))).
  destruct (tm_tp gvtp (l0, l1) th h a).
  simpl in H.
  simpl.
  split.
  reflexivity.
  crush.
  simpl in H.
  discriminate.
  simpl in H.
  discriminate.
  discriminate.
Qed.


Lemma doc_def_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (m : trm)(a : stp),
  check_doc gvtp gvkn th t st (docdef a m::d) = Some (sgn2, imp2) ->
  exists (sgn : gsign),
  (is_norm m) = true /\
  correct_tp 0 a (Z.of_nat (length (fst t))) = true /\
  correct_trm 0 nil sgn m a (fst t) = true /\
  ((exists h, m = TmH h) -> sgn2 = sgn) /\ ( (~exists h, m = TmH h) -> sgn2 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn)) /\
  check_doc gvtp gvkn th t st d = Some(sgn, imp2).
Proof.
  intros.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct p.
  exists g.
  destruct g.
  destruct (is_norm m).
  split.
  crush.
  destruct (correct_tp 0 a (Z.of_nat (length (fst t)))).
  destruct (correct_trm 0 nil (l0, l1) m a (fst t)).
  simpl in H.
  assert (l = imp2).
  destruct m.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  split.
  reflexivity.
  split.
  reflexivity.
  split.
  destruct m.
  intros; destruct H1; discriminate.
  intros; crush.
  intros; destruct H1; discriminate.
  intros; destruct H1; discriminate.
  intros; destruct H1; discriminate.
  intros; destruct H1; discriminate.
  intros; destruct H1; discriminate.
  intros; destruct H1; discriminate.
  intros; destruct H1; discriminate.
  intros; destruct H1; discriminate.
  split.
  intros.
  destruct m.
  crush.
  contradict H1.
  exists h.
  reflexivity.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  rewrite H0.
  reflexivity.
  simpl in H; discriminate.
  simpl in H; discriminate.
  simpl in H; discriminate.
  simpl in H; discriminate.
Qed.
 
Lemma doc_known_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (p : trm),
  check_doc gvtp gvkn th t st (docknown p::d) = Some (sgn2, imp2) ->
  exists (sgn : gsign),
  check_doc gvtp gvkn th t st d = Some(sgn, imp2) /\
  (is_norm p) = true /\
  correct_ptrm 0 sgn p (fst t) = true /\
  sgn2 = (fst sgn, (trm_hashroot p, p) :: snd sgn) /\
  (existsb (fun x => hasheq x (trm_hashroot p)) (snd t) = true \/ known gvkn sgn th (trm_hashroot p) = true).
Proof.
  intros.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct t.
  destruct p0.
  exists g.
  destruct g.
  destruct (is_norm p).
  simpl in H.
  split.
  destruct (correct_ptrm 0 (l2, l3) p l).
  assert (l1 = imp2).
  destruct (existsb (fun x : hashval => hasheq x (trm_hashroot p)) l0).
  crush.
  destruct (prop_of_known l3 (trm_hashroot p)).
  crush.
  destruct (gvkn th (trm_hashroot p)).
  crush.
  discriminate.
  rewrite H0.
  reflexivity.
  discriminate.
  split.
  crush.
  split.
  simpl.
  destruct (correct_ptrm 0 (l2, l3) p l).
  reflexivity.
  discriminate.
  simpl.
  destruct (correct_ptrm 0 (l2, l3) p l).
  destruct (existsb (fun x : hashval => hasheq x (trm_hashroot p)) l0).
  crush.
  destruct (prop_of_known l3 (trm_hashroot p)).
  crush.
  destruct (gvkn th (trm_hashroot p)).
  crush.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed. 

Lemma doc_conj_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (p : trm),
  check_doc gvtp gvkn th t st (docconj p::d) = Some (sgn2, imp2) ->
  check_doc gvtp gvkn th t st d = Some (sgn2, imp2) /\
  (is_norm p) = true /\
  correct_ptrm 0 sgn2 p (fst t) = true.
Proof.
  intros.
  split.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct p0.
  destruct g.
  destruct (is_norm p).
  destruct (correct_ptrm 0 (l0, l1) p (fst t)).
  crush.
  discriminate.
  discriminate.
  discriminate.
  split.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct p0.
  destruct g.
  destruct (is_norm p).
  crush.
  discriminate.
  discriminate.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct p0.
  destruct (is_norm p).
  assert (sgn2 = g).
  destruct (correct_ptrm 0 g p (fst t)).
  crush.
  discriminate.
  rewrite H0.
  destruct (correct_ptrm 0 g p (fst t)).
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
Qed. 


Lemma doc_pfof_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (d:doc) (sgn2 : gsign) (imp2 : list hashval) (p : trm) (e : pf),
  check_doc gvtp gvkn th t st (docpfof p e::d) = Some (sgn2, imp2) ->
  exists (sgn : gsign) (p2 : trm),
  check_doc gvtp gvkn th t st d = Some (sgn, imp2) /\
  sgn2 = (fst sgn, (trm_hashroot p, p) :: snd sgn) /\
  (is_norm p) = true /\
  Some p2 = beta_eta_delta_norm p sgn /\
  correct_pf 0 nil nil sgn e p2 (fst t) = true /\
  correct_ptrm 0 sgn p (fst t) = true.
Proof.
  intros.
  unfold check_doc in H.
  fold check_doc in H.
  destruct (check_doc gvtp gvkn th t st d).
  destruct p0.
  exists g.
  destruct g.
  destruct (is_norm p).
  destruct (correct_ptrm 0 (l0, l1) p (fst t)).
  destruct (correct_pf 0 nil nil (l0, l1) e p (fst t)).
  simpl in H.
  destruct (beta_eta_delta_norm p (l0, l1)).
  exists t0.
  split.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  simpl in H.
  assert (l = imp2).
  crush.
  rewrite H0.
  reflexivity.
  discriminate.
  split.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  unfold snd.
  unfold fst.
  crush.
  discriminate.
  split.
  simpl.
  reflexivity.
  split.
  reflexivity.
  split.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  reflexivity.
  discriminate.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  reflexivity.
  discriminate.
  discriminate.

  destruct (beta_eta_delta_norm p (l0, l1)).
  exists t0.
  split.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  simpl in H.
  assert (l = imp2).
  crush.
  rewrite H0.
  reflexivity.
  discriminate.
  split.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  unfold snd.
  unfold fst.
  crush.
  discriminate.
  split.
  simpl.
  reflexivity.
  split.
  reflexivity.
  split.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  reflexivity.
  discriminate.
  destruct (correct_pf 0 nil nil (l0, l1) e t0 (fst t)).
  reflexivity.
  discriminate.
  discriminate.

  discriminate.
  discriminate.
  discriminate.
Qed.

Theorem doc_eq1 : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (th:option hashval) (t : theory) (st: option stree) (d:doc) (sgn : gsign) (imp : list hashval),
  check_doc gvtp gvkn th t st d = Some (sgn, imp) -> crt_doc gvtp gvkn st th t d sgn imp.
Proof.
  induction d.
  - intros.
    unfold check_doc in H.
    assert (sgn = (nil, nil)).
    crush.
    assert (imp = nil).
    crush.
    rewrite H0.
    rewrite H1.
    apply doc_nil.
  - destruct a.
    + intros.
      apply doc_sign_eq in H.
      destruct H as [sgn0 H].
      destruct H as [imp0 H].
      destruct H as [str H].
      destruct H as [H1 H].
      destruct H as [H2 H3].
      apply IHd in H2.
      apply doc_sign with (str := str) (sgn := sgn0) (imp := imp0).
      apply H2.
      apply H1.
      apply H3.
    + intros.
      apply doc_param_eq in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H4].
      apply IHd in H1.
      apply ptp_eq1 in H3.
      rewrite H4.
      apply doc_param with (sgn := sgn0).
      apply H1.
      apply H3.
      apply H2.
    + intros.
      apply doc_def_eq in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H].
      destruct H as [H5 H6].
      apply IHd in H6.
      apply ptp_eq1 in H2.
      apply crt_trm_eq1 in H3.
      apply doc_def with (sgn := sgn0).
      apply H6.
      apply H1.
      apply H2.
      apply H3.
      apply H4.
      apply H5.
    + intros.
      apply doc_known_eq in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H].
      apply IHd in H1.
      apply ptrm_eq1 in H3.
      rewrite H4.
      apply doc_known.
      apply H1.
      apply H2.
      apply H3.
      rewrite in_find_eq in H.
      apply H.
    + intros.
      apply doc_pfof_eq in H.
      destruct H as [sgn0 H].
      destruct H as [p2 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H].
      destruct H as [H5 H6].
      apply IHd in H1.
      apply ptrm_eq1 in H6.
      apply crt_pf_eq1 in H5.
      rewrite H2.
      apply doc_pf with (p2 := p2).
      apply H1.
      apply H3.
      apply H6.
      apply H4.
      apply H5.
    + intros.
      apply doc_conj_eq in H.
      destruct H as [H1 H].
      destruct H as [H2 H3].
      apply IHd in H1.
      apply ptrm_eq1 in H3.
      apply doc_conj.
      apply H1.
      apply H2.
      apply H3.
Qed.

Theorem doc_eq2 : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (th:option hashval) (t : theory) (st: option stree) (d:doc) (sgn : gsign) (imp : list hashval),
  crt_doc gvtp gvkn st th t d sgn imp -> check_doc gvtp gvkn th t st d = Some (sgn, imp).
Proof.
  induction d.
  - intros.
    apply doc_nil_rev in H.
    unfold check_doc.
    crush.
  - intros.
    destruct a.
    + apply doc_sign_rev in H.
      destruct H as [sgn0 H].
      destruct H as [imp0 H].
      destruct H as [str H].
      destruct H as [H1 H].
      destruct H as [H2 H3].
      apply IHd in H2.
      unfold check_doc.
      fold check_doc.
      rewrite H2.
      rewrite H1.
      rewrite H3.
      reflexivity.
    + apply doc_param_rev in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H4].
      apply IHd in H1.
      unfold check_doc.
      fold check_doc.
      rewrite H1.
      destruct sgn0.
      apply ptp_eq2 in H3.
      rewrite H3.
      rewrite H2.
      simpl.
      crush.
    + apply doc_def_rev in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H].
      destruct H as [H5 H6].
      apply IHd in H6.
      apply ptp_eq2 in H2.
      apply crt_trm_eq2 in H3.
      unfold check_doc.
      fold check_doc.
      rewrite H6.
      destruct sgn0.
      destruct (is_norm t0).
      rewrite H3.
      rewrite H2.
      simpl.
      simpl in H5.
      destruct t0.
      assert (sgn = ((trm_hashroot (DB z), s, Some (DB z)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = (l, l0)).
      apply H4.
      exists h.
      reflexivity.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (Prim z), s, Some (Prim z)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (Ap t0_1 t0_2), s, Some (Ap t0_1 t0_2)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (Lam s0 t0), s, Some (Lam s0 t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (Imp t0_1 t0_2), s, Some (Imp t0_1 t0_2)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (All s0 t0), s, Some (All s0 t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (TTpAp t0 s0), s, Some (TTpAp t0 s0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (TTpLam t0), s, Some (TTpLam t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (TTpAll t0), s, Some (TTpAll t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      discriminate.
    + apply doc_known_rev in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H5].
      apply IHd in H1.
      apply ptrm_eq2 in H3.
     
      unfold check_doc.
      fold check_doc.
      rewrite H1.
      destruct sgn0.
      destruct (is_norm t0).
      rewrite H3.
      destruct t.
      unfold snd in H5.
      unfold snd in H5.
      rewrite <- in_find_eq in H5.
      apply orb_true_intro in H5.
      unfold snd.
      rewrite H5.
      simpl in H4.
      rewrite H4.
      reflexivity.
      discriminate.
    + apply doc_pfof_rev in H.
      destruct H as [sgn0 H].
      destruct H as [p2 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H].
      destruct H as [H5 H6].
      apply IHd in H1.
      apply ptrm_eq2 in H6.
      apply crt_pf_eq2 in H5.
     
      unfold check_doc.
      fold check_doc.
      rewrite H1.
      destruct sgn0.
      destruct (is_norm t0).
      rewrite H6.
      destruct (beta_eta_delta_norm t0 (l, l0)).
      assert (p2 = t1).
      crush.
      rewrite H in H5.
      rewrite H5.
      crush.
      discriminate.
      discriminate.
    + apply doc_conj_rev in H.
      destruct H as [H1 H].
      destruct H as [H2 H3].
      apply IHd in H1.
      apply ptrm_eq2 in H3.
      unfold check_doc.
      fold check_doc.
      rewrite H1.
      destruct (is_norm t0).
      rewrite H3.
      crush.
      simpl in H2.
      discriminate.
Qed.