Require Export DocLogic.
Require Export ProofVerif.
Require Export MathData.
Require Import Bool Arith List Cpdt.CpdtTactics.

Lemma thy_prim_eq : forall (t : theoryspec) (thy0 : theory) (sgn : gsign) (a : stp),
  check_theoryspec (thyprim a ::t) = Some (thy0, sgn) ->
  exists (thy : theory), 
  thy0 = (fst thy ++ a::nil, snd thy) /\
  correct_tp 0 a (Z.of_nat (length (fst thy))) = true /\
  check_theoryspec t = Some (thy, sgn).
Proof.
  intros.
  unfold check_theoryspec in H.
  fold check_theoryspec in H.
  destruct (check_theoryspec t).
  - exists (fst p).
      split.
      destruct p.
      simpl.
      destruct t0.
      simpl.
      destruct (correct_tp 0 a (Z.of_nat (length l))).
      crush.
      discriminate.
      split.
      destruct p.
      simpl.
      destruct t0.
      simpl.
      destruct (correct_tp 0 a (Z.of_nat (length l))).
      reflexivity.
      discriminate.
      destruct p.
      simpl.
      destruct t0.
      simpl.
      destruct (correct_tp 0 a (Z.of_nat (length l))).
      crush.
      discriminate.
      - discriminate.
Qed.


Lemma thy_axiom_eq : forall (t : theoryspec) (thy0 : theory) (sgn0 : gsign) (p : trm),
  check_theoryspec (thyaxiom p::t) = Some (thy0, sgn0) ->
  exists (thy : theory) (sgn : gsign), 
  thy0 = (fst thy, trm_hashroot p :: snd thy) /\
  sgn0 = (fst sgn, (trm_hashroot p, p) :: snd sgn) /\
  correct_ptrm 0 sgn p (fst thy) = true /\
  is_norm p = true /\
  check_theoryspec t = Some (thy, sgn).
Proof.
  intros.
  unfold check_theoryspec in H.
  fold check_theoryspec in H.
  destruct (check_theoryspec t).
  - exists (fst p0); exists (snd p0).
      split.
      destruct p0.
      simpl.
      destruct t.
      simpl.
      destruct t0.
      simpl.
      destruct g.
      simpl.
      destruct (is_norm p).
      destruct (correct_ptrm 0 (l1, l2) p l).
      crush.
      discriminate.
      discriminate.

      destruct t0.
      simpl.
      destruct g.
      simpl.
      destruct (is_norm p).
      destruct (correct_ptrm 0 (l1, l2) p l).
      crush.
      discriminate.
      discriminate.
      
      destruct p0.
      simpl.
      destruct t.
      simpl.
      destruct t0.
      simpl.
      destruct g.
      simpl.
      destruct (is_norm p).
      destruct (correct_ptrm 0 (l1, l2) p l).
      crush.
      discriminate.
      discriminate.

      destruct t0.
      simpl.
      destruct g.
      simpl.
      destruct (is_norm p).
      destruct (correct_ptrm 0 (l1, l2) p l).
      crush.
      discriminate.
      discriminate.
  - discriminate. 
Qed.


Lemma thy_def_eq : forall (t : theoryspec) (sgn0 : gsign) (thy : theory) (m : trm) (a : stp),
  check_theoryspec (thydef a m::t) = Some (thy, sgn0) ->
  exists (sgn : gsign), 
  sgn0 = ((trm_hashroot m, a, Some m) :: fst sgn, snd sgn) /\
  correct_trm 0 nil sgn m a (fst thy) = true /\
  correct_tp 0 a (Z.of_nat (length (fst thy))) = true /\
  is_norm m = true /\
  check_theoryspec t = Some (thy, sgn).
Proof.
  intros.
  unfold check_theoryspec in H.
  fold check_theoryspec in H.
  destruct (check_theoryspec t).
  - exists (snd p).
      split.
      + destruct p.
        simpl.
        destruct t0.
        simpl.
        destruct g.
        simpl.
        destruct (is_norm m).
        destruct (correct_tp 0 a (Z.of_nat (length l))).
        simpl.
        destruct (correct_trm 0 nil (l1, l2) m a l).
        simpl in H.
        crush.
        simpl in H.
        discriminate.
        destruct (correct_trm 0 nil (l1, l2) m a l).
        simpl in H.
        discriminate.
        simpl in H.
        discriminate.
        discriminate.

      + split.
        * destruct p.
          destruct t0.
          destruct g.
          destruct (is_norm m).

          destruct (correct_tp 0 a (Z.of_nat (length l))).
          simpl in H.
          assert (l = fst thy).
          destruct (correct_trm 0 nil (l1, l2) m a l).
          crush.
          discriminate.
          rewrite <- H0.
          simpl.
          destruct (correct_trm 0 nil (l1, l2) m a l).
          reflexivity.
          discriminate.
          simpl in H.
          discriminate.
          discriminate.

        * split.
          destruct p.
          destruct t0.
          simpl.
          destruct g.
          simpl.
          destruct (is_norm m).

          assert (l = fst thy).
          destruct (correct_tp 0 a (Z.of_nat (length l))).
          destruct (correct_trm 0 nil (l1, l2) m a l).
          crush.
          simpl in H.
          discriminate.
          destruct (correct_trm 0 nil (l1, l2) m a l).
          simpl in H.
          discriminate.
          simpl in H.
          discriminate.
          rewrite <- H0.

          destruct (correct_tp 0 a (Z.of_nat (length l))).
          simpl in H.
          destruct (correct_trm 0 nil (l1, l2) m a l).
          crush.
          discriminate.
          simpl in H.
          discriminate.
          discriminate.

          split.
          destruct p.
          destruct t0.
          destruct g.
          destruct (is_norm m).

          destruct (correct_tp 0 a (Z.of_nat (length l))).
          destruct (correct_trm 0 nil (l1, l2) m a l).
          crush.
          simpl in H.
          discriminate.
          destruct (correct_trm 0 nil (l1, l2) m a l).
          simpl in H.
          discriminate.
          simpl in H.
          discriminate.
          discriminate.

          destruct p.
          destruct t0.
          destruct g.
          destruct (is_norm m).

          destruct (correct_tp 0 a (Z.of_nat (length l))).
          destruct (correct_trm 0 nil (l1, l2) m a l).
          crush.
          simpl in H.
          discriminate.
          destruct (correct_trm 0 nil (l1, l2) m a l).
          simpl in H.
          discriminate.
          simpl in H.
          discriminate.
          discriminate.
  - discriminate. 
Qed.

Theorem theoryspec_eq1: forall (thy : theoryspec) (t : theory) (sgn : gsign),
  check_theoryspec thy = Some (t, sgn) -> crt_theoryspec thy t sgn.
Proof.
  induction thy.
  - intros.
    unfold check_theoryspec in H.
    crush.
    apply thy_nil.
  - intros.
    destruct a.
    + apply thy_prim_eq in H.
      destruct H as [thy0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      apply thy_prim with (thy := thy0).
      apply IHthy in H.
      apply H.
      apply ptp_eq1 in H2.
      apply H2.
      apply H1.
    + apply thy_axiom_eq in H.
      destruct H as [thy0 H].
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H5].
      rewrite H1.
      rewrite H2.
      apply thy_axiom with (thy := thy0) (sgn := sgn0).
      apply IHthy in H5.
      apply H5.
      apply ptrm_eq1.
      apply H3.
      apply H4.
    + apply thy_def_eq in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H5].
      rewrite H1.
      apply thy_def with (sgn := sgn0).
      apply IHthy in H5.
      apply H5.
      apply ptp_eq1.
      apply H3.
      apply crt_trm_eq1 in H2.
      apply H2.
      apply H4.
Qed.

Theorem theoryspec_eq2: forall (t : theoryspec) (thy : theory) (sgn : gsign),
  crt_theoryspec t thy sgn -> check_theoryspec t = Some (thy, sgn).
Proof.
  induction t.
  - intros.
    apply thy_nil_rev in H.
    unfold check_theoryspec.
    destruct H as [H1 H2].
    rewrite H1.
    rewrite H2.
    reflexivity.
  - destruct a.
    + intros.
      apply thy_prim_rev in H.
      destruct H as [thy0 H].
      destruct H as [H1 H].
      destruct H as [H2 H3].
      apply IHt in H3.
      apply ptp_eq2 in H1.
      unfold check_theoryspec.
      fold check_theoryspec.
      destruct (check_theoryspec t).
      destruct p.
      assert (t0 = thy0).
      crush.
      assert (g = sgn).
      crush.
      destruct t0.
      assert (l = fst thy0).
      crush.
      assert (l0 = snd thy0).
      rewrite <- H.
      simpl.
      reflexivity.
      rewrite H4.
      destruct (correct_tp 0 s (Z.of_nat (length (fst thy0)))).
      rewrite -> H5.
      rewrite -> H2.
      rewrite -> H0.
      reflexivity.
      discriminate.
      discriminate.
    + intros.
      apply thy_axiom_rev in H.
      destruct H as [thy0 H].
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H5].
     
      apply IHt in H3.
      apply ptrm_eq2 in H4.
      unfold check_theoryspec.
      fold check_theoryspec.

      destruct (check_theoryspec t).
      destruct p.
      destruct g.
      destruct (is_norm t0).
      destruct t1.
      simpl in H5.
      assert (l1 = fst thy0).
      crush.
      assert (l2 = snd thy0).
      crush.
      rewrite <- H0.
      simpl.
      reflexivity.
      rewrite <- H in H4.
      assert ((l, l0) = sgn0).
      crush.
      rewrite <- H6 in H4.
      destruct (correct_ptrm 0 (l, l0) t0 l1).
      rewrite H1.
      rewrite H2.
      rewrite H.
      rewrite H0.
      crush.
      discriminate.
      discriminate.
      discriminate.
    + intros.
      apply thy_def_rev in H.
      destruct H as [sgn0 H].
      destruct H as [H1 H].
      destruct H as [H2 H].
      destruct H as [H3 H].
      destruct H as [H4 H5].
     
      apply IHt in H2.
      apply ptp_eq2 in H3.
      apply crt_trm_eq2 in H4.
      unfold check_theoryspec.
      fold check_theoryspec.
      destruct (check_theoryspec t).
      destruct p.
      destruct t1.
      destruct g.
      destruct (is_norm t0).

      simpl in H5.
      assert (l = fst thy).
      crush.
      rewrite <- H in H3.
      destruct (correct_tp 0 s (Z.of_nat (length l))).
      assert ((l1, l2) = sgn0).
      crush.
      rewrite <- H in H4.
      rewrite <- H0 in H4.
      destruct (correct_trm 0 nil (l1, l2) t0 s l).
      simpl.
      rewrite H1.
      crush.
      discriminate.
      discriminate.
      discriminate.
      discriminate.
Qed.
