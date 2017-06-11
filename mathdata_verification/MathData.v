Require Export DocHash.
Require Export Tree.
Require Export Checking.

Fixpoint check_theoryspec (t : theoryspec) : option (theory * gsign) :=
match t with
  | nil => Some ((nil, nil), (nil, nil))
  | thyaxiom m :: tr =>
    match check_theoryspec tr with
      | None => None
      | Some ((a, b), (c, d)) =>
        match is_norm m with
          | false => None
          | true =>
            if correct_ptrm 0 (c, d) m a then
              let h := trm_hashroot m in
              Some ((a, h::b), (c, (h, m)::d))
            else
              None
        end
    end
  | thydef tp m :: tr =>
    match check_theoryspec tr with
      | None => None
      | Some ((a, b), (c, d)) =>
        match is_norm m with
          | false => None
          | true =>
            let l := Z.of_nat (length a) in
            if correct_tp 0 tp l && correct_trm 0 nil (c, d) m tp a then
              let h := trm_hashroot m in
              Some ((a, b), ((h, tp, Some m)::c, d))
            else
              None
        end
    end
  | thyprim tp :: tr =>
    match check_theoryspec tr with
      | None => None
      | Some ((a, b), c) =>
        if correct_tp 0 tp (Z.of_nat (length a)) then
          Some ((a ++ tp::nil, b), c)
        else
          None
    end
end.

Fixpoint tp_of_tmh (tpl : list (hashval * stp * (option trm))) (h : hashval) : option stp :=
  match tpl with
  | nil => None
  | (k, a, _)::tpr => if hashval_eq_dec h k then Some a else tp_of_tmh tpr h
  end.

Fixpoint tm_tp (gvtp : option hashval -> hashval -> stp -> bool) (sg : gsign) (th : option hashval) (h : hashval) (a : stp) : bool := 
  match sg with
    | (tpl, _) =>
      match tp_of_tmh tpl h with
        | None => gvtp th h a
        | Some b => if stp_eq_dec a b then true else false
      end
  end.

Fixpoint prop_of_known (kl : list (hashval * trm)) (h : hashval) : option trm :=
  match kl with
    | (k, p)::kr => if hashval_eq_dec k h then Some p else prop_of_known kr h
    | nil => None
  end.

Fixpoint known (gvkn : option hashval -> hashval -> bool) (sg : gsign) (th : option hashval) (k : hashval) : bool :=
  match prop_of_known (snd sg) k with
    | Some _ => true
    | None => gvkn th k
  end.

Fixpoint check_signaspec (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (th : option hashval) (t : theory) (tr : option stree) (s : signaspec) : option (gsign * list hashval) :=
  match s with
    | signasigna h :: dr =>
      match check_signaspec gvtp gvkn th t tr dr with
        | None => None
        | Some (sg, imported) =>
          match tr with
	          | Some str => import_signatures th str (h::nil) sg imported
	          | None => None
          end             
      end
    | signaparam h a ::dr =>
      match check_signaspec gvtp gvkn th t tr dr with
        | None => None
        | Some ((tmtpl, kl), imported) => 
          let l := Z.of_nat (length (fst t)) in
          if correct_tp 0 a l && tm_tp gvtp (tmtpl, kl) th h a then
	          Some (((h, a, None)::tmtpl, kl),imported)
          else
	          None
      end
    | signadef a m::dr =>
      match check_signaspec gvtp gvkn th t tr dr with
        | None => None
        | Some ((tmtpl, kl), imported) =>
          match is_norm m with
            | false => None
            | true =>
              let l := Z.of_nat (length (fst t)) in
              if correct_tp 0 a l && correct_trm 0 nil (tmtpl, kl) m a (fst t) then
                let h := trm_hashroot m in
	              match m with
	                | TmH _ => Some ((tmtpl,kl), imported) 
	                | _ => Some (((h,a,Some m)::tmtpl, kl), imported)
                end
              else
                None
          end
      end
    | signaknown p::dr =>
      match check_signaspec gvtp gvkn th t tr dr with
        | None => None
        | Some ((tmtpl, kl), imported) =>
          match is_norm p with
            | false => None
            | true =>
              if correct_ptrm 0 (tmtpl, kl) p (fst t) then
                let k := trm_hashroot p in
	              match t with
	                | (_, akl) =>
	                  if existsb (fun x => hasheq x k) akl || known gvkn (tmtpl,kl) th k then 
	                    Some ((tmtpl, (k,p)::kl), imported)
	                  else
                      None
                end
              else
                None
          end
      end
    | nil => Some ((nil, nil), nil)
end.

Fixpoint check_doc (gvtp : option hashval -> hashval -> stp -> bool) (gvkn : option hashval -> hashval -> bool) (th : option hashval) (thy : theory) (str : option stree) (dl : doc) : option (gsign * list hashval) :=
  match dl with
  | nil => Some ((nil, nil), nil)
  | docsigna h::dr =>
    match check_doc gvtp gvkn th thy str dr with
      | Some (sg, imported) => 
        match str with
          | Some tr => import_signatures th tr (h::nil) sg imported
          | None => None
        end
      | None => None
    end
  | docparam h a::dr =>
    match check_doc gvtp gvkn th thy str dr with
      | Some ((tmtpl,kl), imported) => 
        if correct_tp 0 a (Z.of_nat (length (fst thy))) && tm_tp gvtp (tmtpl,kl) th h a then
            Some (((h, a, None)::tmtpl, kl), imported)
        else
          None
      | None => None
    end
  | docdef a m::dr =>
    match check_doc gvtp gvkn th thy str dr with
      | None => None
      | Some ((tmtpl,kl), imported) => 
        match is_norm m with
          | false => None
          | true =>
            let l := Z.of_nat (length (fst thy)) in
            if correct_tp 0 a l && correct_trm 0 nil (tmtpl, kl) m a (fst thy) then
              let h := trm_hashroot m in
              match m with
                | TmH(_) => Some ((tmtpl,kl),imported) 
                | _ => Some (((h,a,Some(m))::tmtpl,kl),imported)
              end
            else
              None
        end
    end
  | docknown p::dr =>
    match check_doc gvtp gvkn th thy str dr with
      | None => None
      | Some ((tmtpl,kl), imported) => 
        match is_norm p with
          | false => None
          | true =>
            let l := Z.of_nat (length (fst thy)) in
            if correct_ptrm 0 (tmtpl,kl) p (fst thy) then
              let k := trm_hashroot p in
              if existsb (fun x => hasheq x k) (snd thy) || known gvkn (tmtpl, kl) th k then 
                Some ((tmtpl, (k, p):: kl), imported)
              else
                None
            else
              None
        end
    end
  | docconj p::dr =>
    match check_doc gvtp gvkn th thy str dr with
      | None => None
      | Some (sgn, imported) => 
        match is_norm p with
          | false => None
          | true =>
            if correct_ptrm 0 sgn p (fst thy) then
              Some (sgn, imported)
            else
              None
        end
    end
  | docpfof p d::dr =>
    match check_doc gvtp gvkn th thy str dr with
      | None => None
      | Some ((tmtpl,kl), imported) => 
        match is_norm p with
          | false => None
          | true =>
            let k := trm_hashroot p in
            if correct_ptrm 0 (tmtpl, kl) p (fst thy) then
              match (beta_eta_delta_norm p (tmtpl, kl)) with
                | Some p2 =>
                  if correct_pf 0 nil nil (tmtpl, kl) d p2 (fst thy) then
                    Some ((tmtpl, (k, p)::kl), imported)
                  else
                    None
                | None => None
              end
            else
              None
        end
    end
end.

