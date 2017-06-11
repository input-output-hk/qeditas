Require Import Bool.Bool.
Require Import Lists.List.
Require Export Hash.

Parameter redex_amount : nat.

Inductive stp : Type :=
| tpVar : Z -> stp
| base : Z -> stp
| tpAll : stp -> stp
| tpArr : stp -> stp -> stp
| prop : stp.

Fixpoint stp_eq_dec (h1 h2:stp) : { h1 = h2 } + { h1 <> h2 }.
  destruct h1 as [n1|r1|a1|m1 m2|p1]; destruct h2 as [n2|r2|a2|w1 w2|p2]; try (right; discriminate).
  - destruct (Z.eq_dec n1 n2).
    + left. congruence.
    + right. congruence.
  - destruct (Z.eq_dec r1 r2).
    + left. congruence.
    + right. congruence.
  - destruct (stp_eq_dec a1 a2).
    + left. congruence.
    + right. congruence.
  - destruct (stp_eq_dec m1 w1).
    + destruct (stp_eq_dec m2 w2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - intuition.
  Defined.

Inductive trm : Type :=
| DB : Z -> trm
| TmH : hashval -> trm
| Prim : Z -> trm
| Ap : trm -> trm -> trm
| Lam : stp -> trm -> trm
| Imp : trm -> trm -> trm
| All : stp -> trm -> trm
| TTpAp : trm -> stp -> trm
| TTpLam : trm -> trm
| TTpAll : trm -> trm.

Fixpoint trm_eq_dec (h1 h2:trm) : { h1 = h2 } + { h1 <> h2 }.
  destruct h1 as [n1|r1|a1|m1 m2|p1 p2|k1 k2|x1 x2|y1 y2|e1|t1]; destruct h2 as [n2|r2|a2|w1 w2|d1 d2|f1 f2|b1 b2|l1 l2|e2|t2]; try (right; discriminate).
  - destruct (Z.eq_dec n1 n2).
    + left. congruence.
    + right. congruence.
  - destruct (hashval_eq_dec r1 r2).
    + left. congruence.
    + right. congruence.
  - destruct (Z.eq_dec a1 a2).
    + left. congruence.
    + right. congruence.
  - destruct (trm_eq_dec m1 w1).
    + destruct (trm_eq_dec m2 w2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (stp_eq_dec p1 d1).
    + destruct (trm_eq_dec p2 d2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (trm_eq_dec k1 f1).
    + destruct (trm_eq_dec k2 f2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (stp_eq_dec x1 b1).
    + destruct (trm_eq_dec x2 b2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (trm_eq_dec y1 l1).
    + destruct (stp_eq_dec y2 l2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (trm_eq_dec e1 e2).
    + left. congruence.
    + right. congruence.
  - destruct (trm_eq_dec t1 t2).
    + left. congruence.
    + right. congruence.
  Defined.

Inductive pf : Type :=
| Known : hashval -> pf
| Hyp : Z -> pf
| PrAp : pf -> pf -> pf
| TmAp : pf -> trm -> pf
| TpAp : pf -> stp -> pf
| PrLa : trm -> pf -> pf
| TmLa : stp -> pf -> pf
| TpLa : pf -> pf.

Fixpoint pf_eq_dec (h1 h2:pf) : { h1 = h2 } + { h1 <> h2 }.
  destruct h1 as [n1|r1|m1 m2|p1 p2|k1 k2|x1 x2|y1 y2|e1]; destruct h2 as [n2|r2|w1 w2|d1 d2|f1 f2|b1 b2|l1 l2|e2]; try (right; discriminate).
  - destruct (hashval_eq_dec n1 n2).
    + left. congruence.
    + right. congruence.
  - destruct (Z.eq_dec r1 r2).
    + left. congruence.
    + right. congruence.
  - destruct (pf_eq_dec m1 w1).
    + destruct (pf_eq_dec m2 w2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (pf_eq_dec p1 d1).
    + destruct (trm_eq_dec p2 d2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (pf_eq_dec k1 f1).
    + destruct (stp_eq_dec k2 f2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (trm_eq_dec x1 b1).
    + destruct (pf_eq_dec x2 b2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (stp_eq_dec y1 l1).
    + destruct (pf_eq_dec y2 l2).
      * left. congruence.
      * right. congruence.
    + right. congruence.
  - destruct (pf_eq_dec e1 e2).
    + left. congruence.
    + right. congruence.
Defined. 
 
Definition gsign : Type := list (hashval * stp * (option trm)) * list (hashval * trm).

(* Utils *)

Definition first (x : hashval * stp * option trm) : hashval :=
match x with
  | (a, b, c) => a
end.

Fixpoint findsnd2 (k : list (hashval * trm )) (h : hashval) : option trm :=
  match (find (fun x : hashval * trm => hasheq h (fst x)) k) with
    | Some (_, t) => Some t
    | None => None
  end.

Fixpoint findsnd3 (o : list (hashval * stp * (option trm))) (h : hashval) : option stp :=
  match o with
    | nil => None
    | (x, t, _)::l => if hashval_eq_dec x h then Some t else findsnd3 l h
  end.

Fixpoint findthird (k : list (hashval * stp * option trm )) (h : hashval) (def : trm) : trm :=
  match find (fun x : hashval * stp * option trm => hasheq h (first x)) k with
    | Some (_, _, Some t) => t
    | Some (_, _, None) => def
    | None => def 
  end.

(* Lift *)

Fixpoint upstp (t : stp) (i : Z) (j : Z) : stp :=
match t with
  | tpVar k => if (k <? i)%Z then tpVar k else tpVar (k + j)
  | tpArr t1 t2 => tpArr (upstp t1 i j) (upstp t2 i j)
  | tpAll t1 => tpAll (upstp t1 (i + 1) j)
  | _ => t
end.

Fixpoint upstp_trm (t : trm) (i : Z) (j : Z) : trm :=
match t with
  | Ap t1 t2 => Ap (upstp_trm t1 i j) (upstp_trm t2 i j)
  | Lam a1 t1 => Lam (upstp a1 i j) (upstp_trm t1 i j)
  | Imp t1 t2 => Imp (upstp_trm t1 i j) (upstp_trm t2 i j)
  | All b t1 => All (upstp b i j) (upstp_trm t1 i j)
  | TTpAp t1 b => TTpAp (upstp_trm t1 i j) (upstp b i j)
  | TTpLam t1 => TTpLam (upstp_trm t1 (i + 1) j)
  | TTpAll t1 => TTpAll (upstp_trm t1 (i + 1) j)
  | _ => t
end.

Fixpoint uptrm (t : trm) (i : Z) (j : Z) : trm :=
match t with
  | DB k => if (k <? i)%Z then DB k else DB (k + j)
  | Ap t1 t2 => Ap (uptrm t1 i j) (uptrm t2 i j)
  | Lam a1 t1 => Lam a1 (uptrm t1 (i + 1) j)
  | Imp t1 t2 => Imp (uptrm t1 i j) (uptrm t2 i j)
  | All b t1 => All b (uptrm t1 (i + 1) j)
  | TTpAp t1 b => TTpAp (uptrm t1 i j) b
  | TTpLam t1 => TTpLam (uptrm t1 i j)
  | TTpAll t1 => TTpAll (uptrm t1 i j)
  | _ => t
end.

(* Subst *)

Fixpoint subst_stpstp (a : stp) (j : Z) (b : stp) : stp :=
match a with
  | tpVar i => if (j =? i)%Z then
                if (j =? 0)%Z then
                  b
                else
                  upstp b 0 j
              else  
                (if (j <? i)%Z then
                   tpVar (i - 1)
                 else
                   tpVar i)
  | tpAll t1 => tpAll (subst_stpstp t1 (j + 1) b)
  | tpArr t1 t2 => tpArr (subst_stpstp t1 j b) (subst_stpstp t2 j b)
  | _ => a
end.

Fixpoint subst_trmstp (t : trm) (j : Z) (s : stp) : trm :=
match t with
  | Ap t1 t2 => Ap (subst_trmstp t1 j s) (subst_trmstp t2 j s)
  | Lam a1 t1 => Lam (subst_stpstp a1 j s) (subst_trmstp t1 j s)
  | Imp t1 t2 => Imp (subst_trmstp t1 j s) (subst_trmstp t2 j s)
  | All b t1 => All (subst_stpstp b j s) (subst_trmstp t1 j s)
  | TTpAp t1 b => TTpAp (subst_trmstp t1 j s) (subst_stpstp b j s)
  | TTpLam t1 => TTpLam (subst_trmstp t1 (j + 1) s)
  | TTpAll t1 => TTpAll (subst_trmstp t1 (j + 1) s)
  | _ => t
end.

Fixpoint subst_trmtrm (t : trm) (j : Z) (s : trm) : trm :=
match t with
  | DB k => if (k =? j)%Z then
             uptrm s 0 j
           else 
             (if (j <? k)%Z then
               DB (k - 1)
             else
               DB k)
  | Ap t1 t2 => Ap (subst_trmtrm t1 j s) (subst_trmtrm t2 j s)
  | Lam a1 t1 => Lam a1 (subst_trmtrm t1 (j + 1) s)
  | Imp t1 t2 => Imp (subst_trmtrm t1 j s) (subst_trmtrm t2 j s)
  | All b t1 => All b (subst_trmtrm t1 (j + 1) s)
  | TTpAp t1 b => TTpAp (subst_trmtrm t1 j s) b
  | TTpLam t1 => TTpLam (subst_trmtrm t1 j s)
  | TTpAll t1 => TTpAll (subst_trmtrm t1 j s)
  | _ => t
end.

(* Free vars *)

Fixpoint free_trm_trm (t : trm) (i : Z) : bool :=
match t with
  | DB j => (i =? j)%Z
  | Ap m1 m2 => free_trm_trm m1 i || free_trm_trm m2 i
  | Lam a m1 => free_trm_trm m1 (i + 1)
  | Imp m1 m2 => free_trm_trm m1 i || free_trm_trm m2 i
  | All a m1 => free_trm_trm m1 (i + 1)
  | _ => false             
end.

Fixpoint free_stp_stp (t : stp) (i : Z) : bool :=
match t with
  | tpVar j => (i =? j)%Z
  | tpArr a1 a2 => free_stp_stp a1 i || free_stp_stp a2 i
  | tpAll a => free_stp_stp a (i + 1)
  | _ => false
end.

Fixpoint free_stp_trm (t : trm) (i : Z) : bool := 
match t with
  | Ap m1 m2 => free_stp_trm m1 i || free_stp_trm m2 i
  | Lam a m1 => free_stp_stp a i || free_stp_trm m1 i
  | Imp m1 m2 => free_stp_trm m1 i || free_stp_trm m2 i
  | All a m1 => free_stp_stp a i || free_stp_trm m1 i
  | TTpAp m1 a => free_stp_stp a i || free_stp_trm m1 i
  | TTpLam m1 => free_stp_trm m1 (i + 1)
  | TTpAll m1 => free_stp_trm m1 (i + 1)
  | _ => false             
end.

(* Normalization *)

Fixpoint beta_eta_norm1 (t1 : trm) : trm * bool :=
match t1 with
  | Ap m1 m2 => let (t1, r1) := beta_eta_norm1 m1 in
               let (t2, r2) := beta_eta_norm1 m2 in
               match t1 with
                 | Lam a m => (subst_trmtrm m 0 t2, false)
                 | _ => (Ap t1 t2, r1 && r2)
               end
  | Lam a m1 => let (t1, r1) := beta_eta_norm1 m1 in
               match t1 with
                 | Ap m (DB 0) => if free_trm_trm m 0 then (uptrm m 0 (-1), false) else (Lam a t1, r1)
                 | _ => (Lam a t1, r1) 
               end
  | TTpAp m1 a => let (t1, r1) := beta_eta_norm1 m1 in
                 match t1 with
                   | TTpLam m => (subst_trmstp m 0 a, false)
                   | _ => (TTpAp t1 a, r1)
                 end 
  | TTpLam m1 =>  let (t1, r1) := beta_eta_norm1 m1 in
                 match t1 with
                   | TTpAp m (tpVar 0) => if free_stp_trm m 0 then (TTpLam t1, r1) else (upstp_trm m 0 (-1), false)
                   | _ => (TTpLam t1, r1)
                 end
  | Imp m1 m2 => let (t1, r1) := beta_eta_norm1 m1 in
                let (t2, r2) := beta_eta_norm1 m2 in
                (Imp t1 t2, r1 && r2)
  | All a m1 => let (t1, r1) := beta_eta_norm1 m1 in
               (All a t1, r1)
  | TTpAll m1 => let (t1, r1) := beta_eta_norm1 m1 in
               (TTpAll t1, r1)
  | _ => (t1, true)
end.

Fixpoint beta_eta_norm (t1 : trm) (count : nat) : trm * bool :=
match count with
  | O => (t1, false)
  | S n1 => match beta_eta_norm1 t1 with
             | (s, false) => beta_eta_norm s n1
             | a => a
           end
end.

Fixpoint is_norm (m:trm) : bool :=
  match m with
  | Ap (Lam _ _) _  => false
  | TTpAp (TTpLam _) _ => false
  | Lam a (Ap f (DB 0)) => (free_trm_trm f 0) 
  | TTpLam (TTpAp f (tpVar 0)) => (free_stp_trm f 0)
  | Ap m1 m2  => is_norm m1 && is_norm m2
  | Lam a m1  => is_norm m1
  | Imp m1 m2  => is_norm m1 && is_norm m2
  | All a m1  => is_norm m1
  | TTpAp m1 a => is_norm m1
  | TTpLam m1 => is_norm m1
  | TTpAll m1 => is_norm m1
  | _ => true
end.



Fixpoint delta_norm1 (t1 : trm) (sg : gsign) : trm :=
match t1 with
  | TmH h => findthird (fst sg) h t1
  | Ap m1 m2 => Ap (delta_norm1 m1 sg) (delta_norm1 m2 sg)
  | Lam a m1 => Lam a (delta_norm1 m1 sg)
  | Imp m1 m2 => Imp (delta_norm1 m1 sg) (delta_norm1 m2 sg)
  | All a m1 => All a (delta_norm1 m1 sg)
  | TTpAp m1 a => TTpAp (delta_norm1 m1 sg) a
  | TTpLam m1 => TTpLam (delta_norm1 m1 sg)
  | TTpAll m1 => TTpAll (delta_norm1 m1 sg)
  | _ => t1
end.


Fixpoint has_delta_red (t1 : trm) : bool :=
match t1 with
  | TmH h => true
  | Ap m1 m2 => has_delta_red m1 || has_delta_red m2
  | Lam a m1 => has_delta_red m1
  | Imp m1 m2 => has_delta_red m1 || has_delta_red m2
  | All a m1 => has_delta_red m1
  | TTpAp m1 a => has_delta_red m1
  | TTpLam m1 => has_delta_red m1
  | TTpAll m1 => has_delta_red m1
  | _ => false
end.

Fixpoint delta_norm (t1 : trm) (sg : gsign) (count : nat) : trm :=
match count with
  | O => t1
  | S n1 => let t2 := delta_norm1 t1 sg in
    if has_delta_red t2 then delta_norm t2 sg n1 else t2
end.

Fixpoint beta_eta_delta_norm (t : trm) (sg : gsign) : option trm :=
let (s, res) := beta_eta_norm (delta_norm t sg (length (fst sg))) redex_amount in
if res then Some s else None.

(* Correctness *)

Inductive crt_stp : Z -> bool -> Z -> stp -> Prop :=
| tp_all : forall (v : Z) (t : stp) (bt : Z), crt_stp (v + 1) false bt t -> crt_stp v false bt (tpAll t)
| tp_smpl : forall (v : Z) (t : stp)  (bt : Z), crt_stp v true bt t -> crt_stp v false bt t
| stp_arr : forall (v : Z) (t1 : stp) (t2 : stp)  (bt : Z), crt_stp v true bt t1 -> crt_stp v true bt t2 -> crt_stp v true bt (tpArr t1 t2)
| stp_var : forall (v : Z) (n : Z) (bt : Z), (Z.lt n v) -> crt_stp v true bt (tpVar n)
| stp_prop : forall (v : Z) (bt : Z), crt_stp v true bt prop
| stp_base : forall (v : Z) (n : Z) (bt : Z), (Z.lt n bt) -> crt_stp v true bt (base n).

Axiom tp_all_rev : forall (v : Z) (t : stp) (bt : Z), crt_stp v false bt (tpAll t) -> crt_stp (v + 1) false bt t.
Axiom tp_smpl_rev1 : forall (v : Z) (t1 : stp) (t2 : stp) (bt : Z), crt_stp v false bt (tpArr t1 t2) -> crt_stp v true bt (tpArr t1 t2).
Axiom tp_smpl_rev2 : forall (v : Z) (n : Z) (bt : Z), crt_stp v false bt (base n) -> crt_stp v true bt (base n).
Axiom tp_smpl_rev3 : forall (v : Z) (n : Z) (bt : Z), crt_stp v false bt (tpVar n) -> crt_stp v true bt (tpVar n).
Axiom stp_arr_rev1 : forall (v : Z) (t1 : stp) (t2 : stp) (bt : Z), crt_stp v true bt (tpArr t1 t2) -> crt_stp v true bt t1.
Axiom stp_arr_rev2 : forall (v : Z) (t1 : stp) (t2 : stp) (bt : Z), crt_stp v true bt (tpArr t1 t2) -> crt_stp v true bt t2.
Axiom stp_var_rev : forall (v : Z) (n : Z) (bt : Z), crt_stp v true bt (tpVar n) -> (Z.lt n v).
Axiom stp_base_rev : forall (v : Z) (n : Z) (bt : Z), crt_stp v true bt (base n) -> (Z.lt n bt).
Axiom tp_not_stp : forall (v : Z) (t : stp) (bt : Z), ~ crt_stp v true bt (tpAll t). 

Inductive crt_trm : Z -> bool -> list stp -> gsign -> list stp -> trm -> stp -> Prop :=
| trm_db : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign) (i : Z) (t : stp),
             nth_error ctx (Z.to_nat i) = Some t -> crt_trm v true ctx sgn thy (DB i) t
| trm_tmh : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(h : hashval)(t : stp),
              findsnd3 (fst sgn) h = Some t -> crt_trm v true ctx sgn thy (TmH h) t
| trm_prm : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(i : Z) (t : stp),
              nth_error thy (Z.to_nat i) = Some t -> crt_trm v true ctx sgn thy (Prim i) t
| trm_ap : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(a : stp)(b : stp)(s : trm)(t : trm),
             crt_trm v true ctx sgn thy s (tpArr a b) -> crt_trm v true ctx sgn thy t a -> crt_trm v true ctx sgn thy (Ap s t) b 
| trm_lam : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(a : stp)(b : stp)(s : trm),
             crt_stp v true (Z.of_nat (length thy)) a -> crt_trm v true (a::ctx) sgn thy s b -> crt_trm v true ctx sgn thy (Lam a s) (tpArr a b) 
| trm_imp : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(t : trm),
             crt_trm v true ctx sgn thy s prop -> crt_trm v true ctx sgn thy t prop -> crt_trm v true ctx sgn thy (Imp s t) prop 
| trm_all : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(a : stp),
             crt_stp v true (Z.of_nat (length thy)) a -> crt_trm v true (a::ctx) sgn thy s prop -> crt_trm v true ctx sgn thy (All a s) prop 
| trm_tap : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(a : stp)(b : stp),
             crt_stp v true (Z.of_nat (length thy)) b -> crt_trm v true ctx sgn thy s (tpAll a) -> crt_trm v true ctx sgn thy (TTpAp s b) (subst_stpstp a 0 b) 
| trm_tlam : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(a : stp),
             crt_trm (v + 1) true (map (fun x:stp => upstp x 0 1) ctx) sgn thy s a -> crt_trm v true ctx sgn thy (TTpLam s) (tpAll a) 
| trm_simpl : forall (v : Z)(thy : list stp)(sgn : gsign)(s : trm),
             crt_trm v true nil sgn thy s prop -> crt_trm v false nil sgn thy s prop
| trm_tall : forall (v : Z)(thy : list stp)(sgn : gsign)(s : trm),
             crt_trm (v + 1) false nil sgn thy s prop -> crt_trm v false nil sgn thy (TTpAll s) prop.

Axiom trm_db_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign) (i : Z) (t : stp),
   crt_trm v true ctx sgn thy (DB i) t -> nth_error ctx (Z.to_nat i) = Some t. 

Axiom trm_tmh_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(h : hashval)(t : stp),
   crt_trm v true ctx sgn thy (TmH h) t -> findsnd3 (fst sgn) h = Some t. 

Axiom trm_prm_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(i : Z) (t : stp),
  crt_trm v true ctx sgn thy (Prim i) t -> nth_error thy (Z.to_nat i) = Some t.

Axiom trm_ap_rev : forall (v : Z) (ctx : list stp)(thy : list stp)(sgn : gsign)(b : stp)(s : trm)(t : trm),
  crt_trm v true ctx sgn thy (Ap s t) b -> exists (a : stp), crt_trm v true ctx sgn thy s (tpArr a b) /\ crt_trm v true ctx sgn thy t a.

Axiom trm_lam_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(a : stp)(t : stp)(s : trm),
  crt_trm v true ctx sgn thy (Lam a s) t -> exists (b : stp), t = tpArr a b /\ crt_stp v true (Z.of_nat (length thy)) a /\ crt_trm v true (a::ctx) sgn thy s b.

Axiom trm_imp_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(t : trm)(t1 : stp),
  crt_trm v true ctx sgn thy (Imp s t) t1 -> t1 = prop /\ crt_trm v true ctx sgn thy s prop /\ crt_trm v true ctx sgn thy t prop.

Axiom trm_tap_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(t : stp)(b : stp),
  crt_trm v true ctx sgn thy (TTpAp s b) t -> exists (a : stp), t = (subst_stpstp a 0 b) /\ crt_stp v true (Z.of_nat (length thy)) b /\ crt_trm v true ctx sgn thy s (tpAll a). 
Axiom trm_all_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(a : stp) (t:stp),
   crt_trm v true ctx sgn thy (All a s) t -> t = prop /\ crt_stp v true (Z.of_nat (length thy)) a /\ crt_trm v true (a::ctx) sgn thy s prop.

Axiom trm_tlam_rev : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign)(s : trm)(t : stp),
   crt_trm v true ctx sgn thy (TTpLam s) t -> exists (a : stp), t = tpAll a /\ crt_trm (v + 1) true (map (fun x:stp => upstp x 0 1) ctx) sgn thy s a.

Definition isnotTTpAll (t : trm) :=
match t with
  | TTpAll _ => False
  | _ => True
end.

Axiom trm_simpl_rev : forall (v : Z)(thy : list stp)(sgn : gsign)(s : trm)(t:stp),
   crt_trm v false nil sgn thy s t -> isnotTTpAll s -> crt_trm v true nil sgn thy s prop. 

Axiom trm_not_ptrm : forall (v : Z)(ctx : list stp)(thy : list stp)(sgn : gsign) (s : trm) (t : stp),
   crt_trm v true ctx sgn thy (TTpAll s) t -> False. 

Axiom trm_tall_rev : forall (v : Z)(thy : list stp)(sgn : gsign)(s : trm)(t:stp),
   crt_trm v false nil sgn thy (TTpAll s) t -> t = prop /\ crt_trm (v + 1) false nil sgn thy s prop.

Inductive crt_pf : Z -> list stp -> list trm -> gsign -> list stp -> pf -> trm -> Prop :=
| pf_known : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(h : hashval)(s : trm)(t : trm),
  findsnd2 (snd sgn) h = Some s -> beta_eta_delta_norm s sgn = Some t -> crt_pf v ctx phi sgn thy (Known h) t
| pf_hyp : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(i : Z)(t : trm),
  nth_error phi (Z.to_nat i) = Some t -> crt_pf v ctx phi sgn thy (Hyp i) t
| pf_prap : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(e : pf)(s : trm)(t : trm),
  crt_pf v ctx phi sgn thy d (Imp s t) -> crt_pf v ctx phi sgn thy e s -> crt_pf v ctx phi sgn thy (PrAp d e) t
| pf_tmap : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(s : trm)(t : trm)(a : stp)(q : trm),
  crt_pf v ctx phi sgn thy d (All a s) -> crt_trm v true ctx sgn thy t a -> Some q = beta_eta_delta_norm (subst_trmtrm s 0 (delta_norm t sgn (length (fst sgn)))) sgn -> crt_pf v ctx phi sgn thy (TmAp d t) q
| pf_stpap : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(s : trm)(q :trm)(a : stp),
  crt_pf v ctx phi sgn thy d (TTpAll s) -> crt_stp v true (Z.of_nat (length thy)) a -> subst_trmstp s 0 a = q -> crt_pf v ctx phi sgn thy (TpAp d a) q
| pf_tmlam : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(s : trm)(t : trm)(q : trm)(q2 : trm),
  crt_trm v true ctx sgn thy s prop -> Some q = beta_eta_delta_norm s sgn -> crt_pf v ctx (q::phi) sgn thy d t -> q2 = Imp q t -> crt_pf v ctx phi sgn thy (PrLa s d) q2 
| pf_tplam : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(s : trm)(a : stp)(q : trm),
  crt_stp v true (Z.of_nat (length thy)) a -> crt_pf v (a::ctx) (map (fun x:trm => uptrm x 0 1) phi) sgn thy d s -> q = (All a s) -> crt_pf v ctx phi sgn thy (TmLa a d) q  
| pf_all: forall (v : Z)(thy : list stp)(sgn : gsign)(d : pf)(s : trm)(q : trm),
  crt_pf (v + 1) nil nil sgn thy d s -> q = TTpAll s -> crt_pf v nil nil sgn thy (TpLa d) q.

Axiom pf_known_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(h : hashval)(t : trm),
  crt_pf v ctx phi sgn thy (Known h) t -> exists (s : trm), findsnd2 (snd sgn) h = Some s /\ beta_eta_delta_norm s sgn = Some t.

Axiom pf_hyp_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(i : Z)(t : trm),
  crt_pf v ctx phi sgn thy (Hyp i) t -> nth_error phi (Z.to_nat i) = Some t.

Axiom pf_prap_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(e : pf)(t : trm),
  crt_pf v ctx phi sgn thy (PrAp d e) t -> exists (s : trm), crt_pf v ctx phi sgn thy d (Imp s t) /\ crt_pf v ctx phi sgn thy e s.

Axiom pf_tmap_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(t : trm)(q : trm),
crt_pf v ctx phi sgn thy (TmAp d t) q -> exists (s : trm) (a : stp), 
crt_pf v ctx phi sgn thy d (All a s) /\ crt_trm v true ctx sgn thy t a /\ Some q = beta_eta_delta_norm (subst_trmtrm s 0 (delta_norm t sgn (length (fst sgn)))) sgn.

Axiom pf_stpap_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(q :trm)(a : stp),
crt_pf v ctx phi sgn thy (TpAp d a) q -> exists (s : trm),
                                          crt_pf v ctx phi sgn thy d (TTpAll s) /\ crt_stp v true (Z.of_nat (length thy)) a /\ subst_trmstp s 0 a = q.

Axiom pf_tmlam_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(s : trm)(q2 : trm),
  crt_pf v ctx phi sgn thy (PrLa s d) q2 -> exists (t : trm) (q : trm),
  crt_trm v true ctx sgn thy s prop /\ Some q = beta_eta_delta_norm s sgn /\ crt_pf v ctx (q::phi) sgn thy d t /\ q2 = Imp q t.

Axiom pf_tplam_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(a : stp)(q : trm),
crt_pf v ctx phi sgn thy (TmLa a d) q -> exists (s : trm),
  crt_stp v true (Z.of_nat (length thy)) a /\ crt_pf v (a::ctx) (map (fun x:trm => uptrm x 0 1) phi) sgn thy d s /\ q = (All a s).

Axiom pf_all_rev : forall (v : Z)(ctx : list stp)(phi : list trm)(thy : list stp)(sgn : gsign)(d : pf)(q : trm),
crt_pf v ctx phi sgn thy (TpLa d) q -> exists (s : trm), crt_pf (v + 1) ctx phi sgn thy d s /\ q = TTpAll s /\ ctx = nil /\ phi = nil.