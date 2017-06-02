open Logic
open Mathdata


(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match l with
    | [] -> None
    | x :: _ -> Some x)
    (fun n0 ->
    match l with
    | [] -> None
    | _ :: l0 -> nth_error l0 n0)
    n

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x :: tl -> if f x then Some x else find f tl



(** val redex_amount : int **)

let redex_amount = 200

(** val first : ((hashval * stp) * trm option) -> hashval **)

let first = function
| (p, _) -> let (a, _) = p in a

(** val findsnd2 : (hashval * trm) list -> hashval -> trm option **)

let rec findsnd2 k h =
  match find (fun x -> (=) h (fst x)) k with
  | Some p -> let (_, t) = p in Some t
  | None -> None

(** val findsnd3 :
    ((hashval * stp) * trm option) list -> hashval -> stp option **)

let rec findsnd3 o h =
  match o with
  | [] -> None
  | p :: l ->
    let (p0, _) = p in
    let (x, t) = p0 in if (=) x h then Some t else findsnd3 l h

(** val findthird :
    ((hashval * stp) * trm option) list -> hashval -> trm -> trm **)

let rec findthird k h def =
  match find (fun x -> (=) h (first x)) k with
  | Some p ->
    let (_, o) = p in
    (match o with
     | Some t -> t
     | None -> def)
  | None -> def

(** val upstp : stp -> int -> int -> stp **)

let rec upstp t i j =
  match t with
  | TpVar k -> if (<) k i then TpVar k else TpVar ((+) k j)
  | TpAll t1 -> TpAll (upstp t1 ((+) i 1) j)
  | TpArr (t1, t2) -> TpArr ((upstp t1 i j), (upstp t2 i j))
  | _ -> t

(** val upstp_trm : trm -> int -> int -> trm **)

let rec upstp_trm t i j =
  match t with
  | Ap (t1, t2) -> Ap ((upstp_trm t1 i j), (upstp_trm t2 i j))
  | Lam (a1, t1) -> Lam ((upstp a1 i j), (upstp_trm t1 i j))
  | Imp (t1, t2) -> Imp ((upstp_trm t1 i j), (upstp_trm t2 i j))
  | All (b, t1) -> All ((upstp b i j), (upstp_trm t1 i j))
  | TTpAp (t1, b) -> TTpAp ((upstp_trm t1 i j), (upstp b i j))
  | TTpLam t1 -> TTpLam (upstp_trm t1 ((+) i 1) j)
  | TTpAll t1 -> TTpAll (upstp_trm t1 ((+) i 1) j)
  | _ -> t

(** val uptrm : trm -> int -> int -> trm **)

let rec uptrm t i j =
  match t with
  | DB k -> if (<) k i then DB k else DB ((+) k j)
  | Ap (t1, t2) -> Ap ((uptrm t1 i j), (uptrm t2 i j))
  | Lam (a1, t1) -> Lam (a1, (uptrm t1 ((+) i 1) j))
  | Imp (t1, t2) -> Imp ((uptrm t1 i j), (uptrm t2 i j))
  | All (b, t1) -> All (b, (uptrm t1 ((+) i 1) j))
  | TTpAp (t1, b) -> TTpAp ((uptrm t1 i j), b)
  | TTpLam t1 -> TTpLam (uptrm t1 i j)
  | TTpAll t1 -> TTpAll (uptrm t1 i j)
  | _ -> t

(** val subst_stpstp : stp -> int -> stp -> stp **)

let rec subst_stpstp a j b =
  match a with
  | TpVar i ->
    if (=) j i
    then if (=) j 0 then b else upstp b 0 j
    else if (<) j i then TpVar ((-) i 1) else TpVar i
  | TpAll t1 -> TpAll (subst_stpstp t1 ((+) j 1) b)
  | TpArr (t1, t2) -> TpArr ((subst_stpstp t1 j b), (subst_stpstp t2 j b))
  | _ -> a

(** val subst_trmstp : trm -> int -> stp -> trm **)

let rec subst_trmstp t j s =
  match t with
  | Ap (t1, t2) -> Ap ((subst_trmstp t1 j s), (subst_trmstp t2 j s))
  | Lam (a1, t1) -> Lam ((subst_stpstp a1 j s), (subst_trmstp t1 j s))
  | Imp (t1, t2) -> Imp ((subst_trmstp t1 j s), (subst_trmstp t2 j s))
  | All (b, t1) -> All ((subst_stpstp b j s), (subst_trmstp t1 j s))
  | TTpAp (t1, b) -> TTpAp ((subst_trmstp t1 j s), (subst_stpstp b j s))
  | TTpLam t1 -> TTpLam (subst_trmstp t1 ((+) j 1) s)
  | TTpAll t1 -> TTpAll (subst_trmstp t1 ((+) j 1) s)
  | _ -> t

(** val subst_trmtrm : trm -> int -> trm -> trm **)

let rec subst_trmtrm t j s =
  match t with
  | DB k ->
    if (=) k j then uptrm s 0 j else if (<) j k then DB ((-) k 1) else DB k
  | Ap (t1, t2) -> Ap ((subst_trmtrm t1 j s), (subst_trmtrm t2 j s))
  | Lam (a1, t1) -> Lam (a1, (subst_trmtrm t1 ((+) j 1) s))
  | Imp (t1, t2) -> Imp ((subst_trmtrm t1 j s), (subst_trmtrm t2 j s))
  | All (b, t1) -> All (b, (subst_trmtrm t1 ((+) j 1) s))
  | TTpAp (t1, b) -> TTpAp ((subst_trmtrm t1 j s), b)
  | TTpLam t1 -> TTpLam (subst_trmtrm t1 j s)
  | TTpAll t1 -> TTpAll (subst_trmtrm t1 j s)
  | _ -> t

(** val free_trm_trm : trm -> int -> bool **)

let rec free_trm_trm t i =
  match t with
  | DB j -> (=) i j
  | Ap (m1, m2) -> (||) (free_trm_trm m1 i) (free_trm_trm m2 i)
  | Lam (_, m1) -> free_trm_trm m1 ((+) i 1)
  | Imp (m1, m2) -> (||) (free_trm_trm m1 i) (free_trm_trm m2 i)
  | All (_, m1) -> free_trm_trm m1 ((+) i 1)
  | _ -> false

(** val free_stp_stp : stp -> int -> bool **)

let rec free_stp_stp t i =
  match t with
  | TpVar j -> (=) i j
  | TpAll a -> free_stp_stp a ((+) i 1)
  | TpArr (a1, a2) -> (||) (free_stp_stp a1 i) (free_stp_stp a2 i)
  | _ -> false

(** val free_stp_trm : trm -> int -> bool **)

let rec free_stp_trm t i =
  match t with
  | Ap (m1, m2) -> (||) (free_stp_trm m1 i) (free_stp_trm m2 i)
  | Lam (a, m1) -> (||) (free_stp_stp a i) (free_stp_trm m1 i)
  | Imp (m1, m2) -> (||) (free_stp_trm m1 i) (free_stp_trm m2 i)
  | All (a, m1) -> (||) (free_stp_stp a i) (free_stp_trm m1 i)
  | TTpAp (m1, a) -> (||) (free_stp_stp a i) (free_stp_trm m1 i)
  | TTpLam m1 -> free_stp_trm m1 ((+) i 1)
  | TTpAll m1 -> free_stp_trm m1 ((+) i 1)
  | _ -> false

(** val beta_eta_norm1 : trm -> trm * bool **)

let rec beta_eta_norm1 t1 = match t1 with
| Ap (m1, m2) ->
  let (t2, r1) = beta_eta_norm1 m1 in
  let (t3, r2) = beta_eta_norm1 m2 in
  (match t2 with
   | Lam (_, m) -> ((subst_trmtrm m 0 t3), false)
   | _ -> ((Ap (t2, t3)), ((&&) r1 r2)))
| Lam (a, m1) ->
  let (t2, r1) = beta_eta_norm1 m1 in
  (match t2 with
   | Ap (m, t) ->
     (match t with
      | DB z ->
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ ->
           if free_trm_trm m 0
           then ((uptrm m 0 ((~-) 1)), false)
           else ((Lam (a, t2)), r1))
           (fun _ -> ((Lam (a, t2)),
           r1))
           (fun _ -> ((Lam (a, t2)),
           r1))
           z)
      | _ -> ((Lam (a, t2)), r1))
   | _ -> ((Lam (a, t2)), r1))
| Imp (m1, m2) ->
  let (t2, r1) = beta_eta_norm1 m1 in
  let (t3, r2) = beta_eta_norm1 m2 in ((Imp (t2, t3)), ((&&) r1 r2))
| All (a, m1) -> let (t2, r1) = beta_eta_norm1 m1 in ((All (a, t2)), r1)
| TTpAp (m1, a) ->
  let (t2, r1) = beta_eta_norm1 m1 in
  (match t2 with
   | TTpLam m -> ((subst_trmstp m 0 a), false)
   | _ -> ((TTpAp (t2, a)), r1))
| TTpLam m1 ->
  let (t2, r1) = beta_eta_norm1 m1 in
  (match t2 with
   | TTpAp (m, s) ->
     (match s with
      | TpVar z ->
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ ->
           if free_stp_trm m 0
           then ((TTpLam t2), r1)
           else ((upstp_trm m 0 ((~-) 1)), false))
           (fun _ -> ((TTpLam t2),
           r1))
           (fun _ -> ((TTpLam t2),
           r1))
           z)
      | _ -> ((TTpLam t2), r1))
   | _ -> ((TTpLam t2), r1))
| TTpAll m1 -> let (t2, r1) = beta_eta_norm1 m1 in ((TTpAll t2), r1)
| _ -> (t1, true)

(** val beta_eta_norm : trm -> int -> trm * bool **)

let rec beta_eta_norm t1 count =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (t1,
    false))
    (fun n1 ->
    let (s, b) = beta_eta_norm1 t1 in
    if b then (s, true) else beta_eta_norm s n1)
    count

(** val is_norm : trm -> bool **)

let rec is_norm = function
| Ap (m1, m2) ->
  (match m1 with
   | Lam (_, _) -> false
   | _ -> (&&) (is_norm m1) (is_norm m2))
| Lam (_, m1) ->
  (match m1 with
   | Ap (f, t) ->
     (match t with
      | DB z ->
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ ->
           free_trm_trm f 0)
           (fun _ ->
           is_norm m1)
           (fun _ ->
           is_norm m1)
           z)
      | _ -> is_norm m1)
   | _ -> is_norm m1)
| Imp (m1, m2) -> (&&) (is_norm m1) (is_norm m2)
| All (_, m1) -> is_norm m1
| TTpAp (m1, _) ->
  (match m1 with
   | TTpLam _ -> false
   | _ -> is_norm m1)
| TTpLam m1 ->
  (match m1 with
   | TTpAp (f, s) ->
     (match s with
      | TpVar z ->
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ ->
           free_stp_trm f 0)
           (fun _ ->
           is_norm m1)
           (fun _ ->
           is_norm m1)
           z)
      | _ -> is_norm m1)
   | _ -> is_norm m1)
| TTpAll m1 -> is_norm m1
| _ -> true

(** val delta_norm1 : trm -> gsign -> trm **)

let rec delta_norm1 t1 sg =
  match t1 with
  | TmH h -> findthird (fst sg) h t1
  | Ap (m1, m2) -> Ap ((delta_norm1 m1 sg), (delta_norm1 m2 sg))
  | Lam (a, m1) -> Lam (a, (delta_norm1 m1 sg))
  | Imp (m1, m2) -> Imp ((delta_norm1 m1 sg), (delta_norm1 m2 sg))
  | All (a, m1) -> All (a, (delta_norm1 m1 sg))
  | TTpAp (m1, a) -> TTpAp ((delta_norm1 m1 sg), a)
  | TTpLam m1 -> TTpLam (delta_norm1 m1 sg)
  | TTpAll m1 -> TTpAll (delta_norm1 m1 sg)
  | _ -> t1

(** val has_delta_red : trm -> bool **)

let rec has_delta_red = function
| TmH _ -> true
| Ap (m1, m2) -> (||) (has_delta_red m1) (has_delta_red m2)
| Lam (_, m1) -> has_delta_red m1
| Imp (m1, m2) -> (||) (has_delta_red m1) (has_delta_red m2)
| All (_, m1) -> has_delta_red m1
| TTpAp (m1, _) -> has_delta_red m1
| TTpLam m1 -> has_delta_red m1
| TTpAll m1 -> has_delta_red m1
| _ -> false

(** val delta_norm : trm -> gsign -> int -> trm **)

let rec delta_norm t1 sg count =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    t1)
    (fun n1 ->
    let t2 = delta_norm1 t1 sg in
    if has_delta_red t2 then delta_norm t2 sg n1 else t2)
    count

(** val beta_eta_delta_norm : trm -> gsign -> trm option **)

let rec beta_eta_delta_norm t sg =
  let (s, res) =
    beta_eta_norm (delta_norm t sg (List.length (fst sg))) redex_amount
  in
  if res then Some s else None

(** val correct_stp : int -> stp -> int -> bool **)

let rec correct_stp v t base_types =
  match t with
  | TpVar n -> (<) n v
  | Base i -> (<) i base_types
  | TpAll _ -> false
  | TpArr (t1, t2) ->
    (&&) (correct_stp v t1 base_types) (correct_stp v t2 base_types)
  | Prop -> true

(** val correct_tp : int -> stp -> int -> bool **)

let rec correct_tp v t base_types =
  match t with
  | TpAll t1 -> correct_tp ((+) v 1) t1 base_types
  | _ -> correct_stp v t base_types

(** val get_stp_trm :
    int -> stp list -> gsign -> trm -> stp list -> stp option **)

let rec get_stp_trm v ctx sgn t thy =
  match t with
  | DB i -> nth_error ctx ( i)
  | TmH h -> findsnd3 (fst sgn) h
  | Prim i -> nth_error thy ( i)
  | Ap (t1, t2) ->
    (match get_stp_trm v ctx sgn t1 thy with
     | Some s ->
       (match s with
        | TpArr (b, alpha) ->
          (match get_stp_trm v ctx sgn t2 thy with
           | Some b2 -> if (=) b2 b then Some alpha else None
           | None -> None)
        | _ -> None)
     | None -> None)
  | Lam (a1, t1) ->
    if not (correct_stp v a1 ( (List.length thy)))
    then None
    else (match get_stp_trm v (a1 :: ctx) sgn t1 thy with
          | Some b -> Some (TpArr (a1, b))
          | None -> None)
  | Imp (t1, t2) ->
    let a = get_stp_trm v ctx sgn t1 thy in
    let b = get_stp_trm v ctx sgn t2 thy in
    (match a with
     | Some s ->
       (match s with
        | Prop ->
          (match b with
           | Some s0 ->
             (match s0 with
              | Prop -> Some Prop
              | _ -> None)
           | None -> None)
        | _ -> None)
     | None -> None)
  | All (b, t1) ->
    if not (correct_stp v b ( (List.length thy)))
    then None
    else (match get_stp_trm v (b :: ctx) sgn t1 thy with
          | Some s ->
            (match s with
             | Prop -> Some Prop
             | _ -> None)
          | None -> None)
  | TTpAp (t1, b) ->
    if not (correct_stp v b ( (List.length thy)))
    then None
    else (match get_stp_trm v ctx sgn t1 thy with
          | Some s ->
            (match s with
             | TpAll a -> Some (subst_stpstp a 0 b)
             | _ -> None)
          | None -> None)
  | TTpLam t1 ->
    (match get_stp_trm ((+) v 1) (List.map (fun x -> upstp x 0 1) ctx) sgn t1
             thy with
     | Some m -> Some (TpAll m)
     | None -> None)
  | TTpAll _ -> None

(** val correct_trm :
    int -> stp list -> gsign -> trm -> stp -> stp list -> bool **)

let correct_trm v ctx sgn t alpha thy =
  match get_stp_trm v ctx sgn t thy with
  | Some b -> if (=) b alpha then true else false
  | None -> false

(** val correct_ptrm : int -> gsign -> trm -> stp list -> bool **)

let rec correct_ptrm v sgn t thy =
  match t with
  | TTpAll t1 -> correct_ptrm ((+) v 1) sgn t1 thy
  | _ -> correct_trm v [] sgn t Prop thy

(** val get_prop_pf :
    int -> stp list -> trm list -> gsign -> pf -> stp list -> trm option **)

let rec get_prop_pf v ctx phi sg p thy =
  match p with
  | Known h ->
    (match findsnd2 (snd sg) h with
     | Some s -> beta_eta_delta_norm s sg
     | None -> None)
  | Hyp i -> nth_error phi ( i)
  | PrAp (p1, p2) ->
    (match get_prop_pf v ctx phi sg p1 thy with
     | Some t ->
       (match t with
        | Imp (t1, t2) ->
          (match get_prop_pf v ctx phi sg p2 thy with
           | Some m -> if (=) t1 m then Some t2 else None
           | None -> None)
        | _ -> None)
     | None -> None)
  | TmAp (p1, t1) ->
    (match get_prop_pf v ctx phi sg p1 thy with
     | Some t ->
       (match t with
        | All (a, m) ->
          (match get_stp_trm v ctx sg t1 thy with
           | Some b ->
             if (=) a b
             then beta_eta_delta_norm
                    (subst_trmtrm m 0
                      (delta_norm t1 sg (List.length (fst sg)))) sg
             else None
           | None -> None)
        | _ -> None)
     | None -> None)
  | TpAp (p1, a1) ->
    (match get_prop_pf v ctx phi sg p1 thy with
     | Some t ->
       (match t with
        | TTpAll p0 ->
          if correct_stp v a1 ( (List.length thy))
          then Some (subst_trmstp p0 0 a1)
          else None
        | _ -> None)
     | None -> None)
  | PrLa (s, p1) ->
    if not (correct_trm v ctx sg s Prop thy)
    then None
    else (match beta_eta_delta_norm s sg with
          | Some q ->
            (match get_prop_pf v ctx (q :: phi) sg p1 thy with
             | Some q2 -> Some (Imp (q, q2))
             | None -> None)
          | None -> None)
  | TmLa (a1, p1) ->
    if not (correct_stp v a1 ( (List.length thy)))
    then None
    else (match get_prop_pf v (a1 :: ctx)
                  (List.map (fun x -> uptrm x 0 1) phi) sg p1 thy with
          | Some m -> Some (All (a1, m))
          | None -> None)
  | TpLa p1 ->
    (match ctx with
     | [] ->
       (match phi with
        | [] ->
          (match get_prop_pf ((+) v 1) ctx phi sg p1 thy with
           | Some q -> Some (TTpAll q)
           | None -> None)
        | _ :: _ -> None)
     | _ :: _ -> None)

(** val correct_pf :
    int -> stp list -> trm list -> gsign -> pf -> trm -> stp list -> bool **)

let correct_pf v ctx phi sg p t thy =
  match get_prop_pf v ctx phi sg p thy with
  | Some l -> if (=) l t then true else false
  | None -> false

(** val check_theoryspec : theoryspec -> (theory * gsign) option **)

let rec check_theoryspec = function
| [] -> Some (([], []), ([], []))
| t0 :: tr ->
  (match t0 with
   | Thyprim tp ->
     (match check_theoryspec tr with
      | Some p ->
        let (t1, c) = p in
        let (a, b) = t1 in
        if correct_tp 0 tp ( (List.length a))
        then Some ((((@) a (tp :: [])), b), c)
        else None
      | None -> None)
   | Thyaxiom m ->
     (match check_theoryspec tr with
      | Some p ->
        let (t1, g) = p in
        let (a, b) = t1 in
        let (c, d) = g in
        if is_norm m
        then if correct_ptrm 0 (c, d) m a
             then let h = tm_hashroot m in
                  Some ((a, (h :: b)), (c, ((h, m) :: d)))
             else None
        else None
      | None -> None)
   | Thydef (tp, m) ->
     (match check_theoryspec tr with
      | Some p ->
        let (t1, g) = p in
        let (a, b) = t1 in
        let (c, d) = g in
        if is_norm m
        then let l =  (List.length a) in
             if (&&) (correct_tp 0 tp l) (correct_trm 0 [] (c, d) m tp a)
             then let h = tm_hashroot m in
                  Some ((a, b), ((((h, tp), (Some m)) :: c), d))
             else None
        else None
      | None -> None))

(** val tp_of_tmh :
    ((hashval * stp) * trm option) list -> hashval -> stp option **)

let rec tp_of_tmh tpl h =
  match tpl with
  | [] -> None
  | p :: tpr ->
    let (p0, _) = p in
    let (k, a) = p0 in if (=) h k then Some a else tp_of_tmh tpr h

(** val tm_tp :
    (hashval option -> hashval -> stp -> bool) -> gsign -> hashval option ->
    hashval -> stp -> bool **)

let rec tm_tp gvtp sg th h a =
  let (tpl, _) = sg in
  (match tp_of_tmh tpl h with
   | Some b -> if (=) a b then true else false
   | None -> gvtp th h a)

(** val prop_of_known : (hashval * trm) list -> hashval -> trm option **)

let rec prop_of_known kl h =
  match kl with
  | [] -> None
  | p0 :: kr ->
    let (k, p) = p0 in if (=) k h then Some p else prop_of_known kr h

(** val known :
    (hashval option -> hashval -> bool) -> gsign -> hashval option -> hashval
    -> bool **)

let rec known gvkn sg th k =
  match prop_of_known (snd sg) k with
  | Some _ -> true
  | None -> gvkn th k

(** val check_signaspec :
    (hashval option -> hashval -> stp -> bool) -> (hashval option -> hashval
    -> bool) -> hashval option -> theory -> stree option -> signaspec ->
    (gsign * hashval list) option **)

let rec check_signaspec gvtp gvkn th t tr = function
| [] -> Some (([], []), [])
| s0 :: dr ->
  (match s0 with
   | Signasigna h ->
     (match check_signaspec gvtp gvkn th t tr dr with
      | Some p ->
        let (sg, imported) = p in
        (match tr with
         | Some str -> import_signatures th str (h :: []) sg imported
         | None -> None)
      | None -> None)
   | Signaparam (h, a) ->
     (match check_signaspec gvtp gvkn th t tr dr with
      | Some p ->
        let (g, imported) = p in
        let (tmtpl, kl) = g in
        let l =  (List.length (fst t)) in
        if (&&) (correct_tp 0 a l) (tm_tp gvtp (tmtpl, kl) th h a)
        then Some (((((h, a), None) :: tmtpl), kl), imported)
        else None
      | None -> None)
   | Signadef (a, m) ->
     (match check_signaspec gvtp gvkn th t tr dr with
      | Some p ->
        let (g, imported) = p in
        let (tmtpl, kl) = g in
        if is_norm m
        then let l =  (List.length (fst t)) in
             if (&&) (correct_tp 0 a l)
                  (correct_trm 0 [] (tmtpl, kl) m a (fst t))
             then let h = tm_hashroot m in
                  (match m with
                   | TmH _ -> Some ((tmtpl, kl), imported)
                   | _ ->
                     Some (((((h, a), (Some m)) :: tmtpl), kl), imported))
             else None
        else None
      | None -> None)
   | Signaknown p ->
     (match check_signaspec gvtp gvkn th t tr dr with
      | Some p0 ->
        let (g, imported) = p0 in
        let (tmtpl, kl) = g in
        if is_norm p
        then if correct_ptrm 0 (tmtpl, kl) p (fst t)
             then let k = tm_hashroot p in
                  let (_, akl) = t in
                  if (||) (List.exists (fun x -> (=) x k) akl)
                       (known gvkn (tmtpl, kl) th k)
                  then Some ((tmtpl, ((k, p) :: kl)), imported)
                  else None
             else None
        else None
      | None -> None))

(** val check_doc :
    (hashval option -> hashval -> stp -> bool) -> (hashval option -> hashval
    -> bool) -> hashval option -> theory -> stree option -> doc ->
    (gsign * hashval list) option **)

let rec check_doc gvtp gvkn th thy str = function
| [] -> Some (([], []), [])
| d0 :: dr ->
  (match d0 with
   | Docsigna h ->
     (match check_doc gvtp gvkn th thy str dr with
      | Some p ->
        let (sg, imported) = p in
        (match str with
         | Some tr -> import_signatures th tr (h :: []) sg imported
         | None -> None)
      | None -> None)
   | Docparam (h, a) ->
     (match check_doc gvtp gvkn th thy str dr with
      | Some p ->
        let (g, imported) = p in
        let (tmtpl, kl) = g in
        if (&&) (correct_tp 0 a ( (List.length (fst thy))))
             (tm_tp gvtp (tmtpl, kl) th h a)
        then Some (((((h, a), None) :: tmtpl), kl), imported)
        else None
      | None -> None)
   | Docdef (a, m) ->
     (match check_doc gvtp gvkn th thy str dr with
      | Some p ->
        let (g, imported) = p in
        let (tmtpl, kl) = g in
        if is_norm m
        then let l =  (List.length (fst thy)) in
             if (&&) (correct_tp 0 a l)
                  (correct_trm 0 [] (tmtpl, kl) m a (fst thy))
             then let h = tm_hashroot m in
                  (match m with
                   | TmH _ -> Some ((tmtpl, kl), imported)
                   | _ ->
                     Some (((((h, a), (Some m)) :: tmtpl), kl), imported))
             else None
        else None
      | None -> None)
   | Docknown p ->
     (match check_doc gvtp gvkn th thy str dr with
      | Some p0 ->
        let (g, imported) = p0 in
        let (tmtpl, kl) = g in
        if is_norm p
        then if correct_ptrm 0 (tmtpl, kl) p (fst thy)
             then let k = tm_hashroot p in
                  if (||) (List.exists (fun x -> (=) x k) (snd thy))
                       (known gvkn (tmtpl, kl) th k)
                  then Some ((tmtpl, ((k, p) :: kl)), imported)
                  else None
             else None
        else None
      | None -> None)
   | Docpfof (p, d) ->
     (match check_doc gvtp gvkn th thy str dr with
      | Some p0 ->
        let (g, imported) = p0 in
        let (tmtpl, kl) = g in
        if is_norm p
        then let k = tm_hashroot p in
             if correct_ptrm 0 (tmtpl, kl) p (fst thy)
             then (match beta_eta_delta_norm p (tmtpl, kl) with
                   | Some p2 ->
                     if correct_pf 0 [] [] (tmtpl, kl) d p2 (fst thy)
                     then Some ((tmtpl, ((k, p) :: kl)), imported)
                     else None
                   | None -> None)
             else None
        else None
      | None -> None)
   | Docconj p ->
     (match check_doc gvtp gvkn th thy str dr with
      | Some p0 ->
        let (sgn, imported) = p0 in
        if is_norm p
        then if correct_ptrm 0 sgn p (fst thy)
             then Some (sgn, imported)
             else None
        else None
      | None -> None))
