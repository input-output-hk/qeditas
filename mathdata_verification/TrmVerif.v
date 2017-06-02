Require Export TpVerif.
Require Export ListNth.
Require Import Bool Arith List Cpdt.CpdtTactics.

Lemma appt_eq : forall (v : Z) (ctx : list stp) (sgn : gsign) (thy : list stp) (p1 : trm) (p2 : trm) (t2 : stp), get_stp_trm v ctx sgn (Ap p1 p2) thy = Some t2 -> exists (t1 : stp), get_stp_trm v ctx sgn p2 thy = Some t1 /\ get_stp_trm v ctx sgn p1 thy = Some (tpArr t1 t2).
Proof.
  unfold get_stp_trm.
  fold get_stp_trm.
  intros.
  destruct (get_stp_trm v ctx sgn p1 thy).
  - destruct s.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct (get_stp_trm v ctx sgn p2 thy). 
      * destruct (stp_eq_dec s s1).
        assert (t2 = s2).
        crush.
        exists s1.
        split.
        crush.
        rewrite H0.
        crush.
        discriminate.
      * discriminate.
    + discriminate.
  - discriminate.
Qed.

Lemma lam_eq : forall (v : Z) (ctx : list stp) (sgn : gsign) (thy : list stp) (s : stp) (t : stp) (p : trm), get_stp_trm v ctx sgn (Lam s p) thy = Some (tpArr s t) -> get_stp_trm v (s::ctx) sgn p thy = Some t /\ crt_stp v true (Z.of_nat (length thy)) s.
Proof.
  unfold get_stp_trm.
  fold get_stp_trm.
  intros.
  split.
  - destruct (correct_stp v s (Z.of_nat (length thy))).
    simpl in H.
    destruct (get_stp_trm v (s::ctx) sgn p thy).
    + crush.
    + discriminate.
    + simpl in H.
      discriminate.
  - apply stp_eq1.
    destruct (correct_stp v s (Z.of_nat (length thy))).
    + crush.
    + discriminate.
Qed.

Lemma imp_eq : forall (v : Z) (ctx : list stp) (sgn : gsign) (thy : list stp) (p1 : trm) (p2 : trm), get_stp_trm v ctx sgn (Imp p1 p2) thy = Some prop -> get_stp_trm v ctx sgn p1 thy = Some prop /\ get_stp_trm v ctx sgn p2 thy = Some prop .
Proof.
  unfold get_stp_trm.
  fold get_stp_trm.
  intros.
  - destruct (get_stp_trm v ctx sgn p1 thy).
    destruct s.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct (get_stp_trm v ctx sgn p2 thy).
      destruct s.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * crush.
      * discriminate.
    + destruct (get_stp_trm v ctx sgn p2 thy).
      * discriminate.
      * discriminate.
Qed.


Lemma all_eq : forall (v : Z) (ctx : list stp) (sgn : gsign) (thy : list stp) (p : trm) (a : stp), get_stp_trm v ctx sgn (All a p) thy = Some prop -> get_stp_trm v (a::ctx) sgn p thy = Some prop /\ crt_stp v true (Z.of_nat (length thy)) a.
Proof.
  unfold get_stp_trm.
  fold get_stp_trm.
  intros.
  split.
  - destruct (correct_stp v a (Z.of_nat (length thy))).
    simpl in H.
    destruct (get_stp_trm v (a::ctx) sgn p thy).
    destruct s.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + split.
    + discriminate.
    + simpl in H.
      discriminate.
  - apply stp_eq1.
    destruct (correct_stp v a (Z.of_nat (length thy))).
    crush.
    simpl in H.
    discriminate.
Qed.

Lemma tlam_eq : forall (ctx : list stp) (sgn : gsign) (thy : list stp) (s : trm) (a : stp) (b : stp) (v : Z) ,
get_stp_trm v ctx sgn (TTpLam s) thy = Some (tpAll a) -> get_stp_trm (v + 1) (map (fun x:stp => upstp x 0 1) ctx) sgn s thy = Some a.
Proof.
  unfold get_stp_trm.
  fold get_stp_trm.
  intros.
  - destruct (get_stp_trm (v + 1) (map (fun x:stp => upstp x 0 1) ctx) sgn s thy).
    + crush.
    + discriminate.
Qed.

Lemma tap_eq : forall (v : Z) (ctx : list stp) (sgn : gsign) (thy : list stp) (s : trm) (b : stp) (t : stp),
get_stp_trm v ctx sgn (TTpAp s b) thy = Some t -> exists (a : stp), get_stp_trm v ctx sgn s thy = Some (tpAll a) /\ correct_stp v b (Z.of_nat (length thy)) = true /\ t = subst_stpstp a 0 b.
Proof.
  unfold get_stp_trm.
  fold get_stp_trm.
  intros.
  - destruct (correct_stp v b (Z.of_nat (length thy))).
    simpl in H.
    destruct (get_stp_trm v ctx sgn s thy).
    destruct s0.
    + discriminate.
    + discriminate.
    + exists s0.
      crush.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct (get_stp_trm v ctx sgn s thy).
      simpl in H.
      * discriminate.
      * discriminate.
Qed.

Lemma unfold1 : forall (sgn : gsign) (thy : list stp) (s : trm) (v : Z),
 correct_ptrm v sgn (TTpAll (TTpAll s)) thy = true -> correct_ptrm (v + 1) sgn (TTpAll s) thy = true.
Proof.
  intros.
  crush.
Qed.

Lemma tall_eq : forall (sgn : gsign) (thy : list stp) (s : trm) (v : Z),
correct_ptrm v sgn (TTpAll s) thy = true -> correct_ptrm (v + 1) sgn s thy = true.
Proof.
  induction s.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - unfold correct_ptrm.
    crush.
  - intros.
    apply unfold1 in H.
    apply H.
Qed.

Theorem trm_eq1 : forall (sgn : gsign) (thy : list stp) (p : trm) (ctx : list stp) (t : stp) (v : Z),
  get_stp_trm v ctx sgn p thy = Some t -> crt_trm v true ctx sgn thy p t.
Proof.
  induction p.
  - intros.
    unfold get_stp_trm in H.
    apply trm_db.
    apply H.
  - intros.
    unfold get_stp_trm in H.
    apply trm_tmh.
    apply H.
  - intros.
    unfold get_stp_trm in H.
    apply trm_prm.
    apply H.
  - intros.
    apply appt_eq in H.
    destruct H as [h H].
    assert (a := h).
    apply trm_ap with (a := h).
    destruct H as [H2 H1].
    apply IHp1 in H1.
    apply IHp2 in H2.
    apply H1.
    destruct H as [H2 H1].
    apply IHp1 in H1.
    apply IHp2 in H2.
    apply H2.
  - intros.
    destruct t.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      discriminate.
      discriminate.
      simpl in H.
      discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      discriminate.
      discriminate.
      simpl in H.
      discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      discriminate.
      discriminate.
      simpl in H.
      discriminate.
    + assert (H1 := H).
      unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      * simpl in H.
        destruct (get_stp_trm v (s::ctx) sgn p thy).
        assert (s = t1).
        crush.
        rewrite H0.
        rewrite H0 in H1.
        apply trm_lam.
        apply lam_eq in H1.
        destruct H1 as [T1 T2].
        apply T2.
        apply lam_eq in H1.
        destruct H1 as [T1 T2].
        apply IHp in T1.
        apply T1.
        discriminate.
      * simpl in H.
        discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      discriminate.
      discriminate.
      simpl in H.
      discriminate.
  - intros.
    destruct t.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm v ctx sgn p1 thy).
      destruct s.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * destruct (get_stp_trm v ctx sgn p2 thy).
        destruct s.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
      * discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm v ctx sgn p1 thy).
      destruct s.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * destruct (get_stp_trm v ctx sgn p2 thy).
        destruct s.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
      * discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm v ctx sgn p1 thy).
      destruct s.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * destruct (get_stp_trm v ctx sgn p2 thy).
        destruct s.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
      * discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm v ctx sgn p1 thy).
      destruct s.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * destruct (get_stp_trm v ctx sgn p2 thy).
        destruct s.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
        discriminate.
      * discriminate.
    + apply imp_eq in H.
      destruct H as [H1 H2].
      apply IHp1 in H1.
      apply IHp2 in H2.
      apply trm_imp.
      apply H1.
      apply H2.
  - intros.
    destruct t.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      destruct s0.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      destruct s0.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      destruct s0.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (correct_stp v s (Z.of_nat (length thy))).
      simpl in H.
      destruct (get_stp_trm v (s::ctx) sgn p thy).
      destruct s0.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
    + apply all_eq in H.
      destruct H as [H1 H2].
      apply IHp in H1.
      apply trm_all.
      apply H2.
      apply H1.
  - intros.
    apply tap_eq in H.
    destruct H as [h T].
    destruct T as [T1 T].
    destruct T as [T2 T3].
    rewrite T3.
    apply IHp in T1.
    apply stp_eq1 in T2.
    apply trm_tap.
    crush.
    crush.
  - intros.
    destruct t.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm (v + 1) (map (fun x:stp => upstp x 0 1) ctx) sgn p thy).
      * discriminate.
      * discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm (v + 1) (map (fun x:stp => upstp x 0 1) ctx) sgn p thy).
      * discriminate.
      * discriminate.
    + apply tlam_eq in H.
      apply IHp with (ctx := (map (fun x:stp => upstp x 0 1) ctx)) in H.
      apply trm_tlam.
      apply H.
      apply t.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm (v + 1) (map (fun x:stp => upstp x 0 1) ctx) sgn p thy).
      discriminate.
      discriminate.
    + unfold get_stp_trm in H.
      fold get_stp_trm in H.
      destruct (get_stp_trm (v + 1) (map (fun x:stp => upstp x 0 1) ctx) sgn p thy).
      discriminate.
      discriminate.
  - intros.
    unfold get_stp_trm in H.
    discriminate.
Qed.

Theorem crt_trm_eq1 : forall (sgn : gsign) (thy : list stp) (p : trm) (ctx : list stp) (t : stp) (v : Z),
  correct_trm v ctx sgn p t thy = true -> crt_trm v true ctx sgn thy p t.
Proof.
  intros.
  unfold correct_trm in H.
  apply trm_eq1.
  destruct (get_stp_trm v ctx sgn p thy).
  destruct (stp_eq_dec s t).
  crush.
  discriminate.
  discriminate.
Qed.

Theorem ptrm_eq1 : forall (sgn : gsign) (thy : list stp) (p : trm) (v : Z),
  correct_ptrm v sgn p thy = true -> crt_trm v false nil sgn thy p prop.
Proof.
  induction p.
  - intros.
    unfold correct_ptrm in H.
    unfold correct_trm in H.
    unfold get_stp_trm in H.
    rewrite nth_error_nil in H.
    discriminate.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply trm_simpl.
    apply crt_trm_eq1.
    unfold correct_ptrm in H.
    crush.
  - intros.
    apply tall_eq in H.
    apply IHp in H.
    apply trm_tall.
    crush.
Qed. 

Theorem trm_eq2 : forall (sgn : gsign) (thy : list stp) (p : trm) (ctx : list stp) (t : stp) (v : Z),
  crt_trm v true ctx sgn thy p t -> get_stp_trm v ctx sgn p thy = Some t .
Proof.
  induction p.
  - intros.
    apply trm_db_rev in H.
    unfold get_stp_trm.
    crush.
  - intros.
    apply trm_tmh_rev in H.
    unfold get_stp_trm.
    crush.
  - intros.
    apply trm_prm_rev in H.
    unfold get_stp_trm.
    crush.
  - intros.
    apply trm_ap_rev in H.
    unfold get_stp_trm.
    fold get_stp_trm.
    destruct H as [h T].
    destruct T as [H1 H2].
    apply IHp1 in H1.
    apply IHp2 in H2.
    destruct (get_stp_trm v ctx sgn p1 thy).
    + crush.
      destruct (stp_eq_dec h h).
      * reflexivity.
      * contradict n.
      reflexivity.
    + discriminate.
  - intros.
    apply trm_lam_rev in H.
    destruct H as [h T].
    destruct T as [H1 T].
    destruct T as [H2 H3].
    rewrite H1.
    apply IHp in H3.
    apply stp_eq2 in H2.

    unfold get_stp_trm.
    fold get_stp_trm.
    
    destruct (correct_stp v s (Z.of_nat (length thy))).
    simpl.
    destruct (get_stp_trm v (s::ctx) sgn p thy).
    crush.
    discriminate.
    discriminate.
  - intros.
    apply trm_imp_rev in H.
    destruct H as [H0 T].
    destruct T as [H1 H2].
    rewrite H0.
    apply IHp1 in H1.
    apply IHp2 in H2.

    unfold get_stp_trm.
    fold get_stp_trm.

    destruct (get_stp_trm v ctx sgn p1 thy).
    destruct (get_stp_trm v ctx sgn p2 thy).
    crush.
    discriminate.
    discriminate.
  - intros.
    apply trm_all_rev in H.
    destruct H as [H0 T].
    destruct T as [H1 H2].
    rewrite H0.

    unfold get_stp_trm.
    fold get_stp_trm.

    apply IHp in H2.
    apply stp_eq2 in H1.

    destruct (correct_stp v s (Z.of_nat (length thy))).
    simpl.
    destruct (get_stp_trm v (s::ctx) sgn p thy).
    crush.
    discriminate.
    discriminate.
  - intros.
    apply trm_tap_rev in H.
    destruct H as [h T].
    destruct T as [H1 T].
    destruct T as [H2 H3].
    rewrite H1.

    unfold get_stp_trm.
    fold get_stp_trm.

    apply IHp in H3.
    apply stp_eq2 in H2.

    destruct (correct_stp v s (Z.of_nat (length thy))).
    simpl.
    destruct (get_stp_trm v ctx sgn p thy).
    crush.
    discriminate.
    discriminate.
  - intros.
    apply trm_tlam_rev in H.
    destruct H as [h T].
    destruct T as [H1 H2].
    rewrite H1.
    apply IHp in H2.
    unfold get_stp_trm.
    fold get_stp_trm.
    destruct (get_stp_trm (v + 1) (map (fun x : stp => upstp x 0 1) ctx) sgn p thy).
    crush.
    discriminate.
  - intros.
    apply trm_not_ptrm in H.
    crush.
Qed.

Theorem crt_trm_eq2 : forall (sgn : gsign) (thy : list stp) (p : trm) (ctx : list stp) (t : stp) (v : Z),
  crt_trm v true ctx sgn thy p t -> correct_trm v ctx sgn p t thy = true.
Proof.
  intros.
  unfold correct_trm.
  apply trm_eq2 in H. 
  destruct (get_stp_trm v ctx sgn p thy).
  destruct (stp_eq_dec s t).
  crush.
  crush.
  discriminate.
Qed.

Theorem ptrm_eq2 : forall (sgn : gsign) (thy : list stp) (p : trm) (v : Z),
  crt_trm v false nil sgn thy p prop -> correct_ptrm v sgn p thy = true.
Proof.
  induction p.
  - intros.
    apply trm_simpl_rev in H.
    crush.
    apply trm_db_rev in H.
    assert (H2 := nth_error_nil).
    assert (H2 := H2 stp (Z.to_nat z)).
    crush.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    crush.
    apply trm_tmh_rev in H.
    unfold correct_trm.
    unfold get_stp_trm.
    rewrite H.
    crush.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    crush.
    apply trm_prm_rev in H.
    unfold correct_trm.
    unfold get_stp_trm.
    rewrite H.
    crush.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    apply trm_ap_rev in H.
    destruct H as [T1 T].
    destruct T as [T2 T3].
    apply trm_eq2 in T2.
    apply trm_eq2 in T3.
    unfold correct_ptrm.
    unfold correct_trm.
    unfold get_stp_trm.
    fold get_stp_trm.
    destruct (get_stp_trm v nil sgn p1 thy).
    destruct (get_stp_trm v nil sgn p2 thy).
    crush.
    destruct (stp_eq_dec T1 T1).
    destruct (stp_eq_dec prop prop).
    crush.
    crush.
    crush.
    discriminate.
    discriminate.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    apply trm_lam_rev in H.
    destruct H as [h H].
    destruct H as [T1 T2].
    discriminate.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    apply trm_imp_rev in H.
    destruct H as [T1 T].
    destruct T as [T2 T3].
    unfold correct_ptrm.
    unfold correct_trm.
    apply trm_eq2 in T2.
    apply trm_eq2 in T3.
    unfold get_stp_trm.
    fold get_stp_trm.
    destruct (get_stp_trm v nil sgn p1 thy).
    destruct (get_stp_trm v nil sgn p2 thy).
    crush.
    discriminate.
    discriminate.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    apply trm_all_rev in H.
    destruct H as [T1 T].
    destruct T as [T2 T3].
    apply stp_eq2 in T2.
    apply trm_eq2 in T3.
    unfold correct_ptrm.
    unfold correct_trm.
    unfold get_stp_trm.
    fold get_stp_trm.
    destruct (correct_stp v s (Z.of_nat (length thy))).
    destruct (get_stp_trm v (s::nil) sgn p thy).
    simpl.
    crush.
    simpl.
    discriminate.
    crush.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    apply trm_tap_rev in H.
    destruct H as [h T].
    destruct T as [T2 T].
    destruct T as [T3 T4].
    apply stp_eq2 in T3.
    apply trm_eq2 in T4.
    unfold correct_ptrm.
    unfold correct_trm.
    unfold get_stp_trm.
    fold get_stp_trm.
    destruct (correct_stp v s (Z.of_nat (length thy))).
    simpl.
    destruct (get_stp_trm v nil sgn p thy).
    assert (s0 = tpAll h).
    crush.
    rewrite H.
    rewrite T2.
    destruct (stp_eq_dec (subst_stpstp h 0 s) (subst_stpstp h 0 s)).
    crush.
    crush.
    discriminate.
    simpl.
    discriminate.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_simpl_rev in H.
    apply trm_tlam_rev in H.
    destruct H as [h T].
    destruct T as [T1 T2].
    discriminate.
    unfold isnotTTpAll.
    crush.
  - intros.
    apply trm_tall_rev in H.
    destruct H as [_ H].
    apply IHp in H.
    unfold correct_ptrm.
    crush.
Qed.