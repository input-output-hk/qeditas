Require Import Bool Arith List Cpdt.CpdtTactics.
Require Export TrmVerif.

Lemma pf_known_eq : forall (sgn : gsign) (thy : list stp) (h : hashval) (p : trm) (v : Z) (ctx : list stp) (phi : list trm) ,
get_prop_pf v ctx phi sgn (Known h) thy = Some p -> exists s, beta_eta_delta_norm s sgn = Some p /\ findsnd2 (snd sgn) h = Some s. 
Proof.
  intros.
  unfold get_prop_pf in H.
  destruct (findsnd2 (snd sgn) h).
  exists t.
  split.
  apply H.
  reflexivity.
  discriminate.
Qed.

Lemma pf_prap_eq : forall (sgn : gsign) (thy : list stp) (d : pf) (e : pf) (t : trm) (v : Z) (ctx : list stp) (phi : list trm) ,
get_prop_pf v ctx phi sgn (PrAp d e) thy = Some t -> exists s, get_prop_pf v ctx phi sgn d thy = Some (Imp s t) /\ get_prop_pf v ctx phi sgn e thy = Some s. 
Proof.
  intros.
  unfold get_prop_pf in H.
  fold get_prop_pf in H.
  destruct (get_prop_pf v ctx phi sgn d thy).
  destruct t0.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  destruct (get_prop_pf v ctx phi sgn e thy).
  destruct (trm_eq_dec t0_1 t0).
  exists t0.
  crush.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

Lemma pf_tmap_eq : forall (sgn : gsign) (thy : list stp) (d : pf) (t : trm) (v : Z) (ctx : list stp) (phi : list trm) (q :trm),
get_prop_pf v ctx phi sgn (TmAp d t) thy = Some q -> exists (s : trm) (a : stp),
get_prop_pf v ctx phi sgn d thy = Some (All a s) /\ correct_trm v ctx sgn t a thy = true /\ beta_eta_delta_norm (subst_trmtrm s 0 (delta_norm t sgn (length (fst sgn)))) sgn = Some q.
Proof.
  intros.
  unfold get_prop_pf in H.
  fold get_prop_pf in H.
  destruct (get_prop_pf v ctx phi sgn d thy).
  destruct t0.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  unfold correct_trm.
  destruct (get_stp_trm v ctx sgn t thy).
  destruct (stp_eq_dec s s0).
  exists t0.
  exists s0.
  rewrite e.
  split.
  reflexivity.
  split.
  destruct (stp_eq_dec s0 s0).
  reflexivity.
  contradict n.
  reflexivity.
  apply H.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.


Lemma pf_stpap_eq : forall (sgn : gsign) (thy : list stp) (d : pf) (v : Z) (ctx : list stp) (phi : list trm) (q :trm) (a : stp),
  get_prop_pf v ctx phi sgn (TpAp d a) thy = Some q ->
  exists (s : trm), get_prop_pf v ctx phi sgn d thy = Some (TTpAll s) /\ crt_stp v true (Z.of_nat (length thy)) a /\ subst_trmstp s 0 a = q.
Proof.
  intros.
  unfold get_prop_pf in H.
  fold get_prop_pf in H.
  destruct (get_prop_pf v ctx phi sgn d thy).
  destruct t.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  exists t.
  split.
  reflexivity.
  split.
  apply stp_eq1.
  destruct (correct_stp v a (Z.of_nat (length thy))).
  reflexivity.
  discriminate.
  destruct (correct_stp v a (Z.of_nat (length thy))).
  crush.
  discriminate.
  discriminate.
Qed.

Lemma pf_pflam_eq : forall (sgn : gsign) (thy : list stp) (d : pf) (v : Z) (ctx : list stp) (phi : list trm) (q2 :trm) (s :trm),
  get_prop_pf v ctx phi sgn (PrLa s d) thy = Some q2 ->
  exists (q t : trm), beta_eta_delta_norm s sgn = Some q /\ correct_trm v ctx sgn s prop thy = true /\ q2 = Imp q t /\ get_prop_pf v ctx (q::phi) sgn d thy = Some t.
Proof.
  intros.
  unfold get_prop_pf in H.
  fold get_prop_pf in H.
  destruct (correct_trm v ctx sgn s prop thy).
  simpl in H.
  destruct (beta_eta_delta_norm s sgn).
  exists t.
  destruct (get_prop_pf v ctx (t :: phi) sgn d thy).
  exists t0.
  crush.
  discriminate.
  discriminate.
  simpl in H.
  discriminate.
Qed.

Lemma pf_tmlam_eq : forall (sgn : gsign) (thy : list stp) (d : pf) (v : Z) (ctx : list stp) (phi : list trm) (a : stp) (q :trm),
  get_prop_pf v ctx phi sgn (TmLa a d) thy = Some q ->
  exists (s : trm), get_prop_pf v (a::ctx) (map (fun x:trm => uptrm x 0 1) phi) sgn d thy = Some s /\ q = All a s /\ crt_stp v true (Z.of_nat (length thy)) a.
Proof.
  intros.
  unfold get_prop_pf in H.
  fold get_prop_pf in H.
  destruct (get_prop_pf v (a::ctx) (map (fun x:trm => uptrm x 0 1) phi) sgn d thy).
  exists t.
  split.
  reflexivity.
  split.
  destruct (correct_stp v a (Z.of_nat (length thy))).
  simpl in H.
  crush.
  simpl in H.
  discriminate.
  apply stp_eq1.
  destruct (correct_stp v a (Z.of_nat (length thy))).
  reflexivity.
  simpl in H.
  discriminate.
  destruct (correct_stp v a (Z.of_nat (length thy))).
  simpl in H.
  discriminate.
  simpl in H.
  discriminate.
Qed.

Lemma pf_lam_eq : forall (sgn : gsign) (thy : list stp) (d : pf) (v : Z) (q :trm),
  get_prop_pf v nil nil sgn (TpLa d) thy = Some q ->
  exists (s : trm), q = TTpAll s /\ get_prop_pf (v + 1) nil nil sgn d thy = Some s.
Proof.
  intros.
  unfold get_prop_pf in H.
  fold get_prop_pf in H.
  destruct (get_prop_pf (v + 1) nil nil sgn d thy).
  exists t.
  crush.
  discriminate.
Qed. 
  
Theorem pf_eq1: forall (sgn : gsign) (thy : list stp) (d : pf) (p : trm) (v : Z) (ctx : list stp) (phi : list trm),
  get_prop_pf v ctx phi sgn d thy = Some p -> crt_pf v ctx phi sgn thy d p.
Proof.
  induction d.
  - intros.
    apply pf_known_eq in H.
    destruct H as [s H].
    apply pf_known with (s := s).
    destruct H as [H1 H2].
    intros.
    apply H2.
    destruct H as [H1 H2].
    apply H1.
  - intros.
    unfold get_prop_pf in H.
    apply pf_hyp.
    apply H.
  - intros.
    apply pf_prap_eq in H.
    destruct H as [s H].
    apply pf_prap with (s := s).
    destruct H as [H1 H2].
    apply IHd1 in H1.
    apply H1.
    destruct H as [H1 H2].
    apply IHd2 in H2.
    apply H2.
  - intros.
    apply pf_tmap_eq in H.
    destruct H as [s H].
    destruct H as [a H].
    apply pf_tmap with (s := s) (a := a).
    destruct H as [H1 H].
    apply IHd in H1.
    apply H1.
    destruct H as [H1 H].
    destruct H as [H2 H3].
    apply crt_trm_eq1 in H2.
    apply H2.
    destruct H as [H1 H].
    destruct H as [H2 H3].
    destruct (beta_eta_delta_norm (subst_trmtrm s 0 (delta_norm t sgn (length (fst sgn)))) sgn).
    crush.
    discriminate.
  - intros.
    apply pf_stpap_eq in H.
    destruct H as [t H].
    apply pf_stpap with (s := t).
    destruct H as [H1 H].
    apply IHd in H1.
    apply H1.
    destruct H as [H1 H].
    destruct H as [H2 H].
    apply H2.
    destruct H as [H1 H].
    destruct H as [H2 H3].
    apply H3.
  - intros.
    apply pf_pflam_eq in H.
    destruct H as [q H].
    destruct H as [t0 H].
    destruct H as [H1 H].
    destruct H as [H2 H].
    destruct H as [H3 H4].
    apply pf_tmlam with (q := q) (t := t0).
    apply crt_trm_eq1 in H2.
    apply H2.
    crush.
    apply IHd in H4.
    apply H4.
    apply H3.
  - intros.
    apply pf_tmlam_eq in H.
    destruct H as [s0 H].
    destruct H as [H1 H].
    destruct H as [H2 H3].
    apply pf_tplam with (s := s0).
    crush.
    apply IHd in H1.
    apply H1.
    apply H2.
  - intros.
    destruct ctx; destruct phi.
    apply pf_lam_eq in H.
    destruct H as [s H].
    destruct H as [H1 H2].
    apply pf_all with (s := s).
    apply IHd in H2.
    apply H2.
    apply H1.
    unfold get_prop_pf in H.
    discriminate.
    unfold get_prop_pf in H.
    discriminate.
    unfold get_prop_pf in H.
    discriminate.
Qed.


Theorem crt_pf_eq1: forall (sgn : gsign) (thy : list stp) (d : pf) (p : trm) (v : Z) (ctx : list stp) (phi : list trm),
  correct_pf v ctx phi sgn d p thy = true -> crt_pf v ctx phi sgn thy d p.
Proof.
  intros.
  unfold correct_pf in H.
  fold correct_pf in H.
  apply pf_eq1.
  destruct (get_prop_pf v ctx phi sgn d thy).
  destruct (trm_eq_dec t p).
  crush.
  discriminate.
  discriminate.
Qed.

Theorem pf_eq2: forall (sgn : gsign) (thy : list stp) (d : pf) (p : trm) (v : Z) (ctx : list stp) (phi : list trm),
  crt_pf v ctx phi sgn thy d p -> get_prop_pf v ctx phi sgn d thy = Some p.
Proof.
  induction d.
  - intros.
    apply pf_known_rev in H.
    destruct H as [s H].
    destruct H as [H1 H2].
    unfold get_prop_pf.
    rewrite H1.
    rewrite H2.
    reflexivity.
  - intros.
    apply pf_hyp_rev in H.
    unfold get_prop_pf.
    rewrite H.
    reflexivity.
  - intros.
    apply pf_prap_rev in H.
    destruct H as [s H].
    destruct H as [H1 H2].
    unfold get_prop_pf.
    fold get_prop_pf.
    apply IHd1 in H1.
    apply IHd2 in H2.
    rewrite H1.
    rewrite H2.
    destruct (trm_eq_dec s s).
    reflexivity.
    contradict n.
    reflexivity.
  - intros.
    apply pf_tmap_rev in H.
    destruct H as [s H].
    destruct H as [a H].
    destruct H as [H1 H].
    destruct H as [H2 H3].
    unfold get_prop_pf.
    fold get_prop_pf.
    apply IHd in H1.
    rewrite H1.
    apply trm_eq2 in H2.
    rewrite H2.
    destruct (stp_eq_dec a a).
    rewrite H3.
    reflexivity.
    contradict n.
    reflexivity.
  - intros.
    apply pf_stpap_rev in H.
    destruct H as [t H].
    destruct H as [H1 H].
    destruct H as [H2 H3].
    unfold get_prop_pf.
    fold get_prop_pf.
    apply IHd in H1.
    rewrite H1.
    apply stp_eq2 in H2.
    rewrite H2.
    rewrite H3.
    reflexivity.
  - intros.
    apply pf_tmlam_rev in H.
    destruct H as [t0 H].
    destruct H as [q H].
    destruct H as [H1 H].
    destruct H as [H2 H].
    destruct H as [H3 H4].
    unfold get_prop_pf.
    fold get_prop_pf.
    apply IHd in H3.
    apply crt_trm_eq2 in H1.
    rewrite H1.
    simpl.
    rewrite <- H2.
    rewrite H3.
    rewrite H4.
    reflexivity.
  - intros.
    apply pf_tplam_rev in H.
    destruct H as [t H].
    destruct H as [H1 H].
    destruct H as [H2 H3].
    unfold get_prop_pf.
    fold get_prop_pf.
    apply IHd in H2.
    apply stp_eq2 in H1.
    rewrite H1.
    simpl.
    rewrite H2.
    rewrite H3.
    reflexivity.
  - intros.
    apply pf_all_rev in H.
    destruct H as [t H].
    destruct H as [H1 H].
    destruct H as [H2 H].
    destruct H as [H3 H4].
    unfold get_prop_pf.
    fold get_prop_pf.
    apply IHd in H1.
    rewrite H1.
    rewrite H2.
    rewrite H3.
    rewrite H4.
    reflexivity. 
Qed.

Theorem crt_pf_eq2: forall (sgn : gsign) (thy : list stp) (d : pf) (p : trm) (v : Z) (ctx : list stp) (phi : list trm),
  crt_pf v ctx phi sgn thy d p -> correct_pf v ctx phi sgn d p thy = true.
Proof.
  intros.
  unfold correct_pf.
  apply pf_eq2 in H.
  destruct (get_prop_pf v ctx phi sgn d thy).
  destruct (trm_eq_dec t p).
  crush.
  contradict n.
  crush.
  discriminate.
Qed.