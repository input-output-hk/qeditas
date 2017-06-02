Require Export DocLogic.
Require Export ProofVerif.
Require Export MathData.
Require Import Bool Arith List Cpdt.CpdtTactics.

Lemma sgn_signa_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (h : hashval),
  check_signaspec gvtp gvkn th t st (signasigna h::s) = Some (sgn2, imp2) -> exists (sgn : gsign) (imp : list hashval) (str : stree) ,
  check_signaspec gvtp gvkn th t st s = Some(sgn, imp) /\
  st = Some str /\
  Some (sgn2, imp2) = import_signatures th str (h::nil) sgn imp.
Proof.
  intros.
  unfold check_signaspec in H.
  fold check_signaspec in H.
  destruct (check_signaspec gvtp gvkn th t st s).
  destruct p.
  destruct st.
  exists g. exists l. exists s0.
  split.
  reflexivity.
  split.
  reflexivity.
  rewrite H.
  reflexivity.
  discriminate.
  discriminate.
Qed.

Lemma sgn_param_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (h : hashval)(a : stp),
  check_signaspec gvtp gvkn th t st (signaparam h a::s) = Some (sgn2, imp2) ->
  exists (sgn : gsign),
  check_signaspec gvtp gvkn th t st s = Some(sgn, imp2) /\
  tm_tp gvtp sgn th h a = true /\
  correct_tp 0 a (Z.of_nat (length (fst t))) = true /\
  sgn2 = ((h, a, None)::fst sgn, snd sgn).
Proof.
  intros.
  unfold check_signaspec in H.
  fold check_signaspec in H.
  destruct (check_signaspec gvtp gvkn th t st s).
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


Lemma sgn_def_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (m : trm)(a : stp),
  check_signaspec gvtp gvkn th t st (signadef a m::s) = Some (sgn2, imp2) ->
  exists (sgn : gsign),
  (is_norm m) = true /\
  correct_tp 0 a (Z.of_nat (length (fst t))) = true /\
  correct_trm 0 nil sgn m a (fst t) = true /\
  ((exists h, m = TmH h) -> sgn2 = sgn) /\ ( (~exists h, m = TmH h) -> sgn2 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn)) /\
  check_signaspec gvtp gvkn th t st s = Some(sgn, imp2).
Proof.
  intros.
  unfold check_signaspec in H.
  fold check_signaspec in H.
  destruct (check_signaspec gvtp gvkn th t st s).
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
 
Lemma in_find_eq : forall (h : hashval) (l : list hashval),
  existsb (fun x : hashval => hasheq x h) l = true <-> In h l.
Proof.
  split.
  - induction l.
    intros.
    unfold existsb in H.
    discriminate.
    unfold existsb.
    unfold In.
    intros.
    rewrite hasheq_eq.
    destruct (hasheq a h).
    left.
    reflexivity.
    right.
    crush.
  - induction l.
    intros.
    crush.

    intros.
    unfold In in H.
    unfold existsb.
    rewrite hasheq_eq in H.
    decompose [or] H.
    assert (hasheq a h = true).
    apply H0.
    destruct (hasheq a h).
    crush.
    discriminate.
    crush.
Qed. 

Lemma sgn_known_eq : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn2 : gsign) (imp2 : list hashval) (p : trm),
  check_signaspec gvtp gvkn th t st (signaknown p::s) = Some (sgn2, imp2) ->
  exists (sgn : gsign),
  check_signaspec gvtp gvkn th t st s = Some(sgn, imp2) /\
  (is_norm p) = true /\
  correct_ptrm 0 sgn p (fst t) = true /\
  sgn2 = (fst sgn, (trm_hashroot p, p) :: snd sgn) /\
  (existsb (fun x => hasheq x (trm_hashroot p)) (snd t) = true \/ known gvkn sgn th (trm_hashroot p) = true).
Proof.
  intros.
  unfold check_signaspec in H.
  fold check_signaspec in H.
  destruct (check_signaspec gvtp gvkn th t st s).
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

Theorem signaspec_eq1: forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn : gsign) (imp : list hashval),
  check_signaspec gvtp gvkn th t st s = Some (sgn, imp) -> crt_signaspec gvtp gvkn st th t s sgn imp.
Proof.
  induction s.
  - intros.
    unfold check_signaspec in H.
    assert (sgn = (nil, nil)).
    crush.
    assert (imp = nil).
    crush.
    rewrite H0.
    rewrite H1.
    apply sgn_nil.
  - intros.
    destruct a.
    + apply sgn_signa_eq in H.
      destruct H as [sgn0 H].
      destruct H as [imp0 H].
      destruct H as [str H].
      destruct H as [H1 H].
      destruct H as [H2 H3].
      apply IHs in H1.
      apply sgn_signa with (sgn := sgn0) (imp := imp0) (str := str).
      apply H1.
      apply H2.
      apply H3.
   + apply sgn_param_eq in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H4].
      apply IHs in H1.
      apply sgn_param with (sgn := sgn0).
      apply H1.
      apply ptp_eq1.
      apply H3.
      apply H2.
      rewrite H4.
      reflexivity.
   + apply sgn_def_eq in H.
     destruct H as [sgn0 H].
     destruct H as [H1 H].
     destruct H as [H2 H].
     destruct H as [H3 H].
     destruct H as [H4 H].
     destruct H as [H5 H6].
     apply IHs in H6.
     apply sgn_def with (sgn := sgn0).
     apply H6.
     apply H1.
     apply ptp_eq1.
     apply H2.
     apply crt_trm_eq1.
     apply H3.
     intros.
     apply (H4 H).
     intros.
     unfold not in H5.
     unfold not in H.
     apply (H5 H).
   + apply sgn_known_eq in H.
     destruct H as [sgn0 H].
     destruct H as [H1 H].
     destruct H as [H2 H].
     destruct H as [H3 H].
     destruct H as [H4 H5].
     rewrite H4.
     apply sgn_known.
     apply IHs in H1.
     apply H1.
     apply H2.
     apply ptrm_eq1.
     apply H3.
     decompose [or] H5.
     apply in_find_eq in H.
     left.
     apply H.
     right.
     apply H.
Qed.

Theorem signaspec_eq2 : forall (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (st: option stree) (th:option hashval) (t : theory) (s:signaspec) (sgn : gsign) (imp : list hashval),
  crt_signaspec gvtp gvkn st th t s sgn imp -> check_signaspec gvtp gvkn th t st s = Some (sgn, imp).
Proof.
  induction s.
  - intros.
    apply sgn_nil_rev in H.
    unfold check_signaspec.
    crush.
  - intros.
    destruct a.
    + apply sgn_signa_rev in H.
      destruct H as [sgn0 H].
      destruct H as [imp0 H].
      destruct H as [str H].
      destruct H as [H1 H].
      destruct H as [H2 H3].
      apply IHs in H1.
      unfold check_signaspec.
      fold check_signaspec.
      rewrite H1.
      rewrite H2.
      rewrite H3.
      reflexivity.
    + apply sgn_param_rev in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H4].
      apply IHs in H1.
      unfold check_signaspec.
      fold check_signaspec.
      rewrite H1.
      destruct sgn0.
      apply ptp_eq2 in H3.
      rewrite H3.
      rewrite H2.
      simpl.
      crush.
    + apply sgn_def_rev in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H].
      destruct H as [H5 H6].
      apply IHs in H6.
      apply ptp_eq2 in H2.
      apply crt_trm_eq2 in H3.
      unfold check_signaspec.
      fold check_signaspec.
      rewrite H6.
      destruct sgn0.
      destruct (is_norm t0).
      rewrite H3.
      rewrite H2.
      simpl.
      simpl in H5.
      destruct t0.
      assert (sgn = ((trm_hashroot (DB z), s0, Some (DB z)) :: l, l0)).
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
      assert (sgn = ((trm_hashroot (Prim z), s0, Some (Prim z)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (Ap t0_1 t0_2), s0, Some (Ap t0_1 t0_2)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (Lam s1 t0), s0, Some (Lam s1 t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (Imp t0_1 t0_2), s0, Some (Imp t0_1 t0_2)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (All s1 t0), s0, Some (All s1 t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (TTpAp t0 s1), s0, Some (TTpAp t0 s1)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (TTpLam t0), s0, Some (TTpLam t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      assert (sgn = ((trm_hashroot (TTpAll t0), s0, Some (TTpAll t0)) :: l, l0)).
      apply H5.
      crush.
      rewrite H.
      reflexivity.
      discriminate.
    + apply sgn_known_rev in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H5].
      apply IHs in H1.
      apply ptrm_eq2 in H3.
     
      unfold check_signaspec.
      fold check_signaspec.
      rewrite H1.
      destruct sgn0.
      destruct (is_norm t0).
      rewrite H3.
      destruct t.
      unfold snd in H5.
      unfold snd in H5.
      rewrite <- in_find_eq in H5.
      apply orb_true_intro in H5.
      rewrite H5.
      simpl in H4.
      rewrite H4.
      reflexivity.
      discriminate.
Qed.