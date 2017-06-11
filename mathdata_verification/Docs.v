Require Export Logic.

Inductive theoryitem : Type :=
| thyprim : stp -> theoryitem
| thyaxiom : trm -> theoryitem
| thydef : stp -> trm -> theoryitem.

Definition theoryspec : Type := list theoryitem.

Definition theory : Type := (list stp) * (list hashval).

Inductive signaitem : Type :=
| signasigna : hashval -> signaitem
| signaparam : hashval -> stp -> signaitem
| signadef : stp -> trm -> signaitem
| signaknown : trm -> signaitem.

Definition signaspec : Type := list signaitem.

Definition signa : Type := (list hashval) * gsign.

Inductive docitem : Type :=
| docsigna : hashval -> docitem
| docparam : hashval -> stp -> docitem
| docdef : stp -> trm -> docitem
| docknown : trm -> docitem
| docpfof : trm -> pf -> docitem
| docconj : trm -> docitem.

Definition doc : Type := list docitem.

Inductive pdoc : Type :=
| pdoc_nil : pdoc
| pdoc_hash : hashval -> pdoc
| pdoc_signa : hashval -> pdoc -> pdoc
| pdoc_param : hashval -> stp -> pdoc -> pdoc
| pdoc_param_hash : hashval -> pdoc -> pdoc
| pdoc_def : stp -> trm -> pdoc -> pdoc
| pdoc_def_hash : hashval -> pdoc -> pdoc
| pdoc_known : trm -> pdoc -> pdoc
| pdoc_conj : trm -> pdoc -> pdoc
| pdoc_pfof : trm -> pf -> pdoc -> pdoc
| pdoc_pfof_hash : hashval -> pdoc -> pdoc.


Definition theoryitem_eq_dec (d d':theoryitem) : {d = d'} + {d <> d'}.
  destruct d as [a|p|t]; destruct d' as [a'|p'|t']; try (right; discriminate).
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition theoryspec_eq_dec (dl dl':theoryspec) : {dl = dl'} + {dl <> dl'}.
  revert dl'. induction dl as [|d dl IH]; intros [|d' dl']; try (right; discriminate).
  - left. reflexivity.
  - destruct (theoryitem_eq_dec d d') as [D1|D1].
    + destruct (IH dl') as [D2|D2].
      * left. congruence.
      * right. intros H1. inversion H1. tauto.
    + right. intros H1. inversion H1. tauto.
Defined.

Definition signaitem_eq_dec (d d':signaitem) : {d = d'} + {d <> d'}.
  destruct d as [h|h a|a m|p]; destruct d' as [h'|h' a'|a' m'|p']; try (right; discriminate).
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition signaspec_eq_dec (dl dl':signaspec) : {dl = dl'} + {dl <> dl'}.
  revert dl'. induction dl as [|d dl IH]; intros [|d' dl']; try (right; discriminate).
  - left. reflexivity.
  - destruct (signaitem_eq_dec d d') as [D1|D1].
    + destruct (IH dl') as [D2|D2].
      * left. congruence.
      * right. intros H1. inversion H1. tauto.
    + right. intros H1. inversion H1. tauto.
Defined.

Definition docitem_eq_dec (d d':docitem) : {d = d'} + {d <> d'}.
  destruct d as [h|h a|a m|p|p d|t]; destruct d' as [h'|h' a'|a' m'|p'|p' d'|t']; try (right; discriminate).
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
  - repeat decide equality; try apply hashval_eq_dec.
Defined.

Definition doc_eq_dec (dl dl':doc) : {dl = dl'} + {dl <> dl'}.
  revert dl'. induction dl as [|d dl IH]; intros [|d' dl']; try (right; discriminate).
  - left. reflexivity.
  - destruct (docitem_eq_dec d d') as [D1|D1].
    + destruct (IH dl') as [D2|D2].
      * left. congruence.
      * right. intros H1. inversion H1. tauto.
    + right. intros H1. inversion H1. tauto.
Defined.

