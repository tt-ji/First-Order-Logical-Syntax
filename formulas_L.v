(** formulas *)

Require Import base.

Inductive Formula : Type:=
  | X : nat -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula.

Notation "¬ q" := (Not q)(at level 5,right associativity).
Notation "p → q" := (Contain p q)(at level 8,right associativity).

Definition Φ := @ Empty_set Formula.

Ltac ES := 
  match goal with
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?p0 ∈ [?p] |- _ => apply Single in H; rewrite H in *; ES
  | H: ?a ∈ (?B ∪ ?C) |- _ => apply UnionI in H; ES
  | |- ?a ∈ (?B ∪ ?C) => apply UnionI; ES
  | H: ?B \/ ?C |- _ => destruct H; ES
  | H: ?B /\ ?C |- _ => destruct H; ES
  | |- forall a, ?Q => intros; ES
  | |- ?P <-> ?Q => split; intros; ES
  | |- _ => eauto with sets
  end.
