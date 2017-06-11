Require Import Bool.Bool.
Require Import ZArith.Int.
Require Import ZArith.

Require Import Logic.

Fixpoint correct_stp (v: Z) (t : stp) (base_types : Z) : bool :=
  match t with
  | base i => (i <? base_types)%Z
  | tpVar n => (n <? v)%Z
  | tpArr t1 t2 => correct_stp v t1 base_types && correct_stp v t2 base_types
  | tpAll _ => false
  | _ => true
  end.

Fixpoint correct_tp (v: Z) (t : stp) (base_types : Z) : bool :=
match t with
  | tpAll t1 => correct_tp (v + 1) t1 base_types
  | _ => correct_stp v t base_types
end.

Fixpoint get_stp_trm (v : Z) (ctx : list stp) (sgn : gsign) (t : trm) (thy : list stp) : option stp :=
match t with
  | DB i => nth_error ctx (Z.to_nat i) 
  | TmH h => findsnd3 (fst sgn) h
  | Prim i => nth_error thy (Z.to_nat i)
  | Ap t1 t2 => match get_stp_trm v ctx sgn t1 thy, get_stp_trm v ctx sgn t2 thy with
                 | Some (tpArr b alpha), Some b2 => if stp_eq_dec b2 b then Some alpha else None
                 | _, _ => None
               end
  | Lam a1 t1 => if negb (correct_stp v a1 (Z.of_nat (length thy))) then None else
                  match get_stp_trm v (a1::ctx) sgn t1 thy with
                    | Some b => Some (tpArr a1 b)
                    | _ => None
                  end
  | Imp t1 t2 => let a := get_stp_trm v ctx sgn t1 thy in
                let b := get_stp_trm v ctx sgn t2 thy in
                match a, b with
                  | Some prop, Some prop => Some prop
                  | _, _ => None
                end
  | All b t1 => if negb (correct_stp v b (Z.of_nat (length thy))) then None else
                 match get_stp_trm v (b::ctx) sgn t1 thy with
                   | Some prop => Some prop
                   | _ => None
                 end
  | TTpAp t1 b => if negb (correct_stp v b (Z.of_nat (length thy))) then None else
                   match get_stp_trm v ctx sgn t1 thy with
                     | Some (tpAll a) => Some (subst_stpstp a 0 b)
                     | _ => None
                   end
  | TTpLam t1 => match get_stp_trm (v + 1) (map (fun x:stp => upstp x 0 1) ctx) sgn t1 thy with
                  | Some m => Some (tpAll m)
                  | _ => None
                end
  | _ => None
end.

Definition correct_trm (v : Z) (ctx : list stp) (sgn : gsign) (t : trm) (alpha : stp) (thy : list stp) : bool :=
  match get_stp_trm v ctx sgn t thy with
    | Some b => if stp_eq_dec b alpha then true else false 
    | None => false
  end.

Fixpoint correct_ptrm (v : Z) (sgn : gsign) (t : trm) (thy : list stp) : bool :=
match t with
  | TTpAll t1 => correct_ptrm (v + 1) sgn t1 thy
  | _ => correct_trm v nil sgn t prop thy
end.

Fixpoint get_prop_pf (v : Z) (ctx : list stp) (phi : list trm) (sg :gsign) (p : pf) (thy : list stp) : option trm :=
match p with
  | Known h => match findsnd2 (snd sg) h with
                | Some s => beta_eta_delta_norm s sg
                | _ => None
              end
  | Hyp i => nth_error phi (Z.to_nat i)
  | PrAp p1 p2 => match get_prop_pf v ctx phi sg p1 thy with
                   | Some (Imp t1 t2) =>
                     match get_prop_pf v ctx phi sg p2 thy with
                       | Some m => if trm_eq_dec t1 m then Some t2 else None
                       | _ => None
                     end
                   | _ => None
                 end
  | TmAp p1 t1 => match get_prop_pf v ctx phi sg p1 thy, get_stp_trm v ctx sg t1 thy with
                   | Some (All a m), Some b =>
                     if stp_eq_dec a b then
                       beta_eta_delta_norm (subst_trmtrm m 0 (delta_norm t1 sg (length (fst sg)))) sg
                     else None
                   | _, _ => None
                 end
  | TpAp p1 a1 => match get_prop_pf v ctx phi sg p1 thy with
                   | Some (TTpAll p) =>
                     if correct_stp v a1 (Z.of_nat (length thy)) then
                       Some (subst_trmstp p 0 a1)
                     else
                       None
                   | _ => None
                 end
  | TmLa a1 p1 => if negb (correct_stp v a1 (Z.of_nat (length thy))) then None else
                   match get_prop_pf v (a1::ctx) (map (fun x:trm => uptrm x 0 1) phi) sg p1 thy with
                     | Some m => Some (All a1 m)
                     | _ => None
                   end
  | PrLa s p1 => if negb (correct_trm v ctx sg s prop thy) then None else
                  match beta_eta_delta_norm s sg with
                    | None => None
                    | Some q =>
                      match get_prop_pf v ctx (q::phi) sg p1 thy with
                        | Some q2 => Some (Imp q q2)
                        | _ => None
                      end
                  end
  | TpLa p1 => match ctx, phi with
                | nil, nil => match get_prop_pf (v + 1) ctx phi sg p1 thy with
                               | Some q => Some (TTpAll q)
                               | _ => None
                             end
               | _, _ => None
              end
end.

Definition correct_pf (v : Z) (ctx : list stp) (phi : list trm) (sg :gsign) (p : pf) (t : trm) (thy : list stp) : bool :=
  match get_prop_pf v ctx phi sg p thy with 
    | Some l => if trm_eq_dec l t then true else false
    | None => false
  end.