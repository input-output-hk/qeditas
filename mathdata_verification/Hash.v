Require Export Coq.Lists.List.
Require Export Coq.Arith.Peano_dec.
Require Export omega.Omega.
Require Export Bool.Bool.

Parameter hashval : Type.

Parameter hasheq : hashval -> hashval -> bool.
Axiom hasheq_eq : forall (h1 h2:hashval), h1 = h2 <-> hasheq h1 h2 = true.
Parameter prhasheq : hashval * hashval -> hashval * hashval -> bool.

Parameter hashval_eq_dec : forall (h1 h2 : hashval), { h1 = h2 } + { h1 <> h2 }.
