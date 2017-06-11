Require Export Logic.
Require Export Checking.

Lemma arr_eq1 (v : Z) (t1 : stp) (t2 : stp) (bt : Z) :
  correct_stp v (tpArr t1 t2) bt = true -> correct_stp v t1 bt = true.
Proof.
  unfold correct_stp.
  intros.
  apply andb_true_iff in H.
  destruct H.
  apply H.
Qed.

Lemma arr_eq2 (v : Z) (t1 : stp) (t2 : stp) (bt : Z) :
  correct_stp v (tpArr t1 t2) bt = true -> correct_stp v t2 bt = true.
Proof.
  unfold correct_stp.
  intros.
  apply andb_true_iff in H.
  destruct H.
  apply H0.
Qed.

Lemma all_eq (v : Z) (t1 : stp) (bt : Z) :
  correct_tp v (tpAll t1) bt = true -> correct_tp (v + 1) t1 bt = true.
Proof.
  unfold correct_tp.
  intros.
  destruct H.
  intuition.
Qed.

Lemma smpl_eq (v : Z) (t : stp) (bt : Z) :
  correct_stp v t bt = true -> correct_tp v t bt = true.
Proof.
  destruct t.
  - intros.
    unfold correct_tp.
    intuition.
  - intros.
    unfold correct_tp.
    intuition.
  - intros.
    unfold correct_tp.
    unfold correct_stp in H.
    contradict H.
    intuition.
  - intros.
    unfold correct_tp.
    apply H.
  - intros.
    unfold correct_tp.
    apply H.
Qed.

Theorem stp_eq1: forall (t : stp) (bt : Z) (v : Z),
  correct_stp v t bt = true -> crt_stp v true bt t.
Proof.
  induction t.
  - unfold correct_stp.
    intros.
    apply stp_var.
    unfold Z.ltb in H.
    unfold Z.lt.
    destruct (z ?= v)%Z.
    + contradict H.
      intuition.
    + reflexivity.
    + contradict H.
      intuition.
  - unfold correct_stp.
    intros.
    apply stp_base.
    unfold Z.ltb in H.
    unfold Z.lt.
    destruct (z ?= bt)%Z.
    + contradict H.
      intuition.
    + reflexivity.
    + contradict H.
      intuition.
  - unfold correct_stp.
    intros.
    contradict H.
    intuition.
  - intros.
    apply stp_arr.
    + apply arr_eq1 in H.
      apply IHt1.
      apply H.
    + apply arr_eq2 in H.
      apply IHt2.
      apply H.
  - intros.
    apply stp_prop.
Qed.

Theorem ptp_eq1:
forall (bt : Z) (t : stp) (v : Z),  correct_tp v t bt = true -> crt_stp v false bt t.
Proof.
  induction t.
  intros.
  - intros.
    apply tp_smpl.
    apply stp_eq1.
    apply H.
  - intros.
    apply tp_smpl.
    apply stp_eq1.
    apply H.
  - intros.
    apply tp_all.
    apply all_eq in H.
    apply IHt.
    apply H.
  - intros.
    apply tp_smpl.
    assert (H1 := H).
    assert (H2 := H).
    unfold correct_tp in H.
    unfold correct_tp in H1.
    unfold correct_tp in H2.
    apply arr_eq1 in H1.
    apply arr_eq2 in H2.
    apply stp_arr.
    destruct t1.
    + apply stp_eq1.
      apply H1.
    + apply stp_eq1.
      apply H1.
    + apply stp_eq1.
      apply H1.
    + apply stp_eq1.
      apply H1.
    + apply stp_eq1.
      apply H1.
    + apply stp_eq1.
      apply H2.
  - intros.
    apply tp_smpl.
    apply stp_eq1.
    unfold correct_tp in H.
    apply H.
Qed.

Theorem stp_eq2: forall (t : stp) (bt : Z) (v : Z),
  crt_stp v true bt t -> correct_stp v t bt = true.
Proof.
  induction t.
  - intros.
    apply stp_var_rev in H.
    unfold correct_stp.
    unfold Z.lt in H.
    unfold Z.ltb.
    rewrite H.
    intuition.
  - intros.
    apply stp_base_rev in H.
    unfold correct_stp.
    unfold Z.lt in H.
    unfold Z.ltb.
    rewrite H.
    intuition.
  - intros.
    unfold correct_stp.
    apply tp_not_stp in H.
    intuition.
  - intros.
    assert (H1 := H).
    apply stp_arr_rev1 in H.
    apply IHt1 in H.
    apply stp_arr_rev2 in H1.
    apply IHt2 in H1.
    unfold correct_stp.
    intuition.
  - intros.
    unfold correct_stp.
    reflexivity.
Qed.

Theorem ptp_eq2: forall (t : stp) (bt : Z) (v : Z),
  crt_stp v false bt t -> correct_tp v t bt = true.
Proof.
  induction t.
  - intros.
    unfold correct_tp.
    apply stp_eq2.
    apply tp_smpl_rev3.
    apply H.
  - intros.
    unfold correct_tp.
    apply stp_eq2.
    apply tp_smpl_rev2.
    apply H.
  - intros.
    apply tp_all_rev in H.
    apply all_eq.
    apply IHt in H.
    unfold correct_tp.
    intuition.
  - intros.
    apply tp_smpl_rev1 in H.
    unfold correct_tp.
    apply stp_eq2.
    apply H.
  - intros.
    unfold correct_tp.
    unfold correct_stp.
    reflexivity.
Qed.
