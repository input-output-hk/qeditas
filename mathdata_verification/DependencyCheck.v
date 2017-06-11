Require Export DocHash.
Require Export Tree.
Require Export Checking.

Fixpoint theoryspec_primtps (thy:theoryspec) : list stp :=
  match thy with
    | nil => nil
    | thyprim a::thy => theoryspec_primtps thy ++ (a::nil)
    | _::thy => theoryspec_primtps thy
  end.

Definition theoryspec_theory (thy:theoryspec) : theory :=
  (theoryspec_primtps thy, theoryspec_hashedaxioms thy).

Fixpoint signaspec_trms (s:signaspec) : list (hashval * stp * (option trm)) :=
  match s with
    | nil => nil
    | signaparam h a::s => (h, a, None)::signaspec_trms s
    | signadef a m::s => (trm_hashroot m, a, Some m)::signaspec_trms s
    | _::s => signaspec_trms s
  end.

Fixpoint signaspec_knowns (s:signaspec) : list (hashval * trm) :=
  match s with
    | nil => nil
    | signaknown p::s => (trm_hashroot p, p)::signaspec_knowns s
    | _::s => signaspec_knowns s
  end.

Fixpoint signaspec_signas (s:signaspec) : list hashval :=
  match s with
    | nil => nil
    | signasigna h::s => h::signaspec_signas s
    | _::s => signaspec_signas s
  end.

Definition signaspec_signa (s:signaspec) : signa :=
  (signaspec_signas s, (signaspec_trms s, signaspec_knowns s)).

Definition add_unique (h : hashval) (l : list hashval) :=
  let f := fun x => hasheq x h in
  match find f l with
    | None => h::l
    | Some _ => l
  end.

Definition add_unique2 (h : hashval * hashval) (l : list (hashval * hashval)) :=
  let f := fun x => prhasheq x h in
  match find f l with
    | None => h::l
    | Some _ => l
  end.

Fixpoint signaspec_uses_objs (dl:signaspec) : list (hashval * hashval) :=
  match dl with
    | signaparam h a::dr => add_unique2 (h, hash_stp a) (signaspec_uses_objs dr)
    | _::dr => signaspec_uses_objs dr
    | nil => nil
  end.

Fixpoint signaspec_uses_props (dl:signaspec) : list hashval :=
  match dl with
    | signaknown p::dr => add_unique (trm_hashroot p) (signaspec_uses_props dr)
    | _::dr => signaspec_uses_props dr
    | nil => nil
  end.

Fixpoint doc_uses_objs (dl:doc) : list (hashval * hashval) :=
  match dl with
    | docparam h a ::dr => add_unique2 (h, hash_stp a) (doc_uses_objs dr)
    | _::dr => doc_uses_objs dr
    | nil => nil
  end.

Fixpoint doc_uses_props (dl:doc) : list hashval  :=
  match dl with
    | docknown p::dr => add_unique (trm_hashroot p) (doc_uses_props dr)
    | _::dr => doc_uses_props dr
    | nil => nil
  end.

Fixpoint doc_creates_objs (dl:doc) : list (hashval * hashval) :=
  match dl with
    | docdef a m::dr => add_unique2 (trm_hashroot m, hash_stp a) (doc_creates_objs dr)
    | _::dr => doc_creates_objs dr
    | nil => nil
  end.

Fixpoint doc_creates_props (dl:doc) : list (hashval * hashval) :=
  match dl with
    | docpfof p d::dr => add_unique2 (trm_hashroot p, pf_hashroot d) (doc_creates_props dr)
    | _::dr => doc_creates_props dr
    | nil => nil
  end.

Definition falsehashprop : hashval := trm_hashroot (All prop (DB 0)).
Definition neghashprop : hashval := trm_hashroot (Lam prop (Imp (DB 0) (TmH falsehashprop))).

Fixpoint invert_neg_props (t : trm) : option trm :=
  match t with
    | Imp np f => if hashval_eq_dec (trm_hashroot f) falsehashprop then Some np else None 
    | Ap n np => if hashval_eq_dec (trm_hashroot n) neghashprop then Some np else None 
    | _ => None
  end.

Fixpoint doc_creates_neg_props (dl:doc) : list hashval :=
match dl with
  | docpfof p d::dr => match invert_neg_props p with
                          | Some np => add_unique (trm_hashroot np) (doc_creates_neg_props dr)
                          | None => doc_creates_neg_props dr
                      end
  | _ :: dr => doc_creates_neg_props dr
  | nil => nil
end.

  
