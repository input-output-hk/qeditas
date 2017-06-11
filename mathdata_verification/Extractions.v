Require Import Arith Even Div2 EqNat Euclid.
Require Import ZArith NArith.
Require Import Bool.Bool.

Require Import Hash.

Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
Extract Inductive prod => "( * )" [ "" ].

Extract Inductive sumbool => bool [ true false ].
Extract Inductive sumor => option [ Some None ].

Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".
Extract Inlined Constant bool_dec => "(=)".
Extract Inlined Constant negb => "not".

Extract Inductive nat => int [ "0" "succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inlined Constant plus => "(+)".
Extract Inlined Constant pred => "fun n -> max 0 (n-1)".
Extract Inlined Constant minus => "fun n m -> max 0 (n-m)".
Extract Inlined Constant mult => "( * )".
Extract Inlined Constant max => max.
Extract Inlined Constant min => min.
Extract Inlined Constant EqNat.beq_nat => "(=)".
Extract Inlined Constant EqNat.eq_nat_decide => "(=)".

Extract Inlined Constant Peano_dec.eq_nat_dec => "(=)".

Extract Inlined Constant Compare_dec.nat_compare =>
 "fun n m -> if n=m then Eq else if n<m then Lt else Gt".
Extract Inlined Constant Compare_dec.leb => "(<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(<=)".
Extract Inlined Constant Compare_dec.lt_eq_lt_dec =>
 "fun n m -> if n>m then None else Some (n<m)".

Extract Inlined Constant Even.even_odd_dec => "fun n -> n mod 2 = 0".
Extract Inlined Constant Div2.div2 => "fun n -> n/2".

Extract Inductive Euclid.diveucl => "(int * int)" [ "" ].
Extract Inlined Constant Euclid.eucl_dev => "fun n m -> (m/n, m mod n)".
Extract Inlined Constant Euclid.quotient => "fun n m -> m/n".
Extract Inlined Constant Euclid.modulo => "fun n m -> m mod n".

Extract Inductive positive => int
[ "(fun p->1+2*p)" "(fun p->2*p)" "1" ]
"(fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))".

Extract Inductive Z => int [ "0" "" "(~-)" ]
"(fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))".

Extract Inductive N => int [ "0" "" ]
"(fun f0 fp n -> if n=0 then f0 () else fp n)".

Extract Inlined Constant Pos.add => "(+)".
Extract Inlined Constant Pos.succ => "succ".
Extract Inlined Constant Pos.pred => "fun n -> max 1 (n-1)".
Extract Inlined Constant Pos.sub => "fun n m -> max 1 (n-m)".
Extract Inlined Constant Pos.mul => "( * )".
Extract Inlined Constant Pos.min => "min".
Extract Inlined Constant Pos.max => "max".
Extract Inlined Constant Pos.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".
Extract Inlined Constant Pos.compare_cont =>
 "fun x y c -> if x=y then c else if x<y then Lt else Gt".

Extract Inlined Constant N.add => "(+)".
Extract Inlined Constant N.succ => "succ".
Extract Inlined Constant N.pred => "fun n -> max 0 (n-1)".
Extract Inlined Constant N.sub => "fun n m -> max 0 (n-m)".
Extract Inlined Constant N.mul => "( * )".
Extract Inlined Constant N.min => "min".
Extract Inlined Constant N.max => "max".
Extract Inlined Constant N.div => "fun a b -> if b=0 then 0 else a/b".
Extract Inlined Constant N.modulo => "fun a b -> if b=0 then a else a mod b".
Extract Inlined Constant N.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".


Extract Inlined Constant Z.add => "(+)".
Extract Inlined Constant Z.succ => "succ".
Extract Inlined Constant Z.pred => "pred".
Extract Inlined Constant Z.sub => "(-)".
Extract Inlined Constant Z.mul => "( * )".
Extract Inlined Constant Z.opp => "(~-)".
Extract Inlined Constant Z.abs => "abs".
Extract Inlined Constant Z.min => "min".
Extract Inlined Constant Z.max => "max".
Extract Inlined Constant Z.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".

Extract Inlined Constant Z.of_N => "fun p -> p".
Extract Inlined Constant Z.abs_N => "abs".

Extract Inlined Constant Pos.ltb => "(<)".
Extract Inlined Constant Pos.eqb => "(=)".

Extract Inlined Constant Pos.eq_dec => "(=)".
Extract Inlined Constant Pos.to_nat => "".
Extract Inlined Constant N.eq_dec => "(=)".
Extract Inlined Constant N.to_nat => "".

Extract Inlined Constant Z.ltb => "(<)".
Extract Inlined Constant Z.eqb => "(=)".
Extract Inlined Constant Z.eq_dec => "(=)".
Extract Inlined Constant Z.to_nat => "".

Extract Inlined Constant Z.of_N => "fun p -> p".
Extract Inlined Constant Z.abs_N => "abs".

Extract Inlined Constant Pos.add_carry => "".
Extract Inlined Constant Pos.iter_op => "".
Extract Inlined Constant Pos.pred_double => "".
Extract Inlined Constant Pos.of_succ_nat => "".

Extract Inlined Constant Z.double => "".
Extract Inlined Constant Z.succ_double => "".
Extract Inlined Constant Z.pred_double => "".
Extract Inlined Constant Z.pos_sub => "".
Extract Inlined Constant Z.of_nat => "".


Require Export MathData.
Require Export Logic.

Extract Inlined Constant hasheq => "(=)".
Extract Inlined Constant prhasheq => "(=)".
Extract Inlined Constant hashval_eq_dec => "(=)".
Extract Inlined Constant stp_eq_dec => "(=)".
Extract Inlined Constant trm_eq_dec => "(=)".
Extract Inlined Constant pf_eq_dec => "(=)".

Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "(@)".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant existsb => "List.exists".

Extract Inlined Constant hashval => "hashval".
Extract Inlined Constant ttree => "ttree".
Extract Inlined Constant stree => "stree".
Extract Constant redex_amount => "200".
Extract Inlined Constant import_signatures => "import_signatures".
Extract Inlined Constant trm_hashroot => "tm_hashroot".

Extraction "ml/src/logic.ml" stp trm pf doc gsign signa theory theoryspec signaspec.
Extraction "ml/src/checking.ml" stp trm pf doc gsign signa theory theoryspec signaspec check_doc check_signaspec check_theoryspec.

