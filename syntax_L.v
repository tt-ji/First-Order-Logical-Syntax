(** syntax_L *)

Require Import base.
Require Import formulas_L.

Section Propositional_calculus.

Variable Γ : Ensemble Formula.
Inductive deduce_L : Formula -> Prop :=
  | L0 : forall p, p ∈ Γ -> deduce_L p 
  | L1 : forall p q, deduce_L (p → (q → p))
  | L2 : forall p q r, deduce_L ((p → (q → r)) → ((p → q) → (p → r)))
  | L3 : forall p q, deduce_L ((¬p → ¬q)→ (q → p))
  | MP : forall p q, deduce_L (p → q) -> deduce_L p -> deduce_L q.

End Propositional_calculus.

Notation " Γ ├ p " := (deduce_L Γ p)(at level 80).
Global Hint Constructors deduce_L : LD.

Fact Union_l : forall Γ p, Γ ├ p -> forall A, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Fact Union_r : forall Γ p , Γ ├ p -> forall A, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

(*Definition Φ := @ Empty_set Formula.

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
  end. *)

Ltac autoL :=
  match goal with
  | H: ?Γ ├ ?p |- ?Γ ∪ ?A ├ ?p => apply Union_l; auto
  | H: ?Γ ├ ?p |- ?A ∪ ?Γ ├ ?p => apply Union_r; auto
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?Γ ├ ?p , H1: ?Γ ├ ?p → ?q |- ?Γ ├ ?q => apply MP with p; auto
  | H: ?Γ ├ ?p |- ?Γ ├ ?q → ?p => let H0 := fresh in
       assert (H0: Γ ├ p → q → p) by (apply L1); autoL
  | |- ?Γ ├ ?x => eauto with LD sets
  | |- forall a, ?Q => intros; autoL
  end.

Ltac later :=
  match goal with
  | |- ?Γ ├ ?q → ?p => let H0 := fresh in assert (H0: Γ ├ p) by (autoL); autoL
  end.


(* 命题1 同一律 |- p→q *)
Lemma law_identity : forall Γ p, Γ ├ p → p.
Proof. autoL. Unshelve. exact p.  Qed.
Global Hint Resolve law_identity : LD.

(* 命题2 否定前件律 *)
Lemma law_deny_antecedent : forall Γ p q, Γ ├ ¬q → (q → p).
Proof. autoL. Qed.
Global Hint Resolve law_deny_antecedent : LD.

Definition Contradiciton Γ := exists q, Γ ├ q /\ Γ ├ ¬q.

Definition No_Contradiciton Γ := forall q, ~ (Γ ├ q /\ Γ ├ ¬q).

Proposition prop_2_3 : forall Γ, Contradiciton Γ ->  forall p, Γ ├ p.
Proof. intros; destruct H, H; autoL. Qed.

(* 演绎定理 p ├ q  <=>  p → q *)
Theorem Deductive_Theorem : forall Γ p q, Γ∪[p] ├ q <-> Γ ├ p → q.
Proof.
  split; intros.
  - induction H; repeat (autoL; ES).
  - apply MP with p; autoL.
Qed.

Corollary syllogism : forall Γ p q r , Γ ∪ [p] ├ q -> Γ ∪ [r] ├ p -> Γ ∪ [r] ├ q.
Proof.
  intros. apply Deductive_Theorem in H. apply Deductive_Theorem in H0. 
  assert (Γ ∪ [r] ├ r) by autoL. pose proof (Union_l _ _ H [r]). 
  pose proof (Union_l _ _ H0 [r]). autoL.
Qed.

(* 命题1 否定肯定律 (¬p→p)→p *)
Proposition law_negetion_affirmation : forall Γ p, Γ ├ (¬p → p) → p.
Proof.
  intros. apply -> Deductive_Theorem. 
  assert (Γ ∪ [¬ p → p] ├ (¬p → p) → (¬p → ¬(¬p → p))) by autoL.
  assert (Γ ∪ [¬ p → p] ├ ¬p → ¬(¬p → p)) by autoL. autoL.
Qed.
Global Hint Resolve law_negetion_affirmation : LD.


Ltac Single_Union :=
  match goal with 
  | |- ?Γ ∪ [?p] ├ ?q => assert(Γ ∪ [p] ├ p); autoL
  end.

(* 换位律 *)
Fact law_inverse_prop : forall Γ p q, Γ ├ (q → p) → (¬p → ¬q).
Proof.
  intros. apply Deductive_Theorem. assert (Γ ∪ [q → p] ├ ¬¬q → q) by autoL. 
  assert (Γ ∪ [q → p] ├ p → ¬¬p) by autoL. Single_Union. 
  assert (Γ ∪ [q → p] ├ ¬¬q → p) by autoL. autoL.
Qed.

Global Hint Resolve law_inverse_prop : LD.

(*Peirce律*)
Fact law_peirce : forall Γ p q , Γ ├ ((p → q) → p) → p.
Proof.
  intros. apply Deductive_Theorem. assert (Γ ├ ¬p → (p →q)) by
  autoL. apply Union_l with (A:=[(p → q) → p]) in H. Single_Union.
Qed.
Global Hint Resolve law_peirce : LD.

(* 反证律与归谬律 *)
(* 反证律 law of indirect proof *)
Theorem rule_Indirect : forall Γ p q, Γ∪[¬p] ├ q -> Γ∪[¬p] ├ ¬q -> Γ ├ p.
Proof.
  intros. assert (Γ∪[¬p] ├ p) by autoL.
  apply Deductive_Theorem in H1; autoL. Unshelve. auto. auto. auto.
Qed.

(* 反证律推论 双重否定律 *)
Corollary law_double_negation_aux : forall p, [¬¬p] ├ p.
Proof. autoL. Unshelve. auto. Qed.

Corollary law_double_negation : forall  Γ p, Γ ├ ¬¬p → p.
Proof. intros; apply Deductive_Theorem. autoL. Qed.
Global Hint Resolve law_double_negation : LD.

(* 归谬律 law of reduction to absurdity *)
Theorem rule_Reduction_absurdity :
  forall Γ p q, Γ∪[p] ├ q -> Γ∪[p] ├ ¬q -> Γ ├ ¬p.
Proof.
  intros. assert (Γ ∪ [¬¬p] ├ q). { eapply syllogism; autoL. } 
  assert (Γ ∪ [¬¬p] ├ ¬q). { eapply syllogism; autoL. }
  apply (rule_Indirect _ _ _ H1 H2); auto.
Qed.