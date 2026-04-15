(** syntax_K *)

Require Import base.
Require Import formulas_K.

Section Predicate_Calculus.

(* 公理系统 *)
Inductive Axiom_system : Formula -> Prop :=
  | P1 : forall p q, Axiom_system (p → (q → p))
  | P2 : forall p q r, Axiom_system ((p → (q → r)) → ((p → q) → (p → r)))
  | P3 : forall p q, Axiom_system ((¬p → q) → ((¬p → ¬q) → p))
  | S' : forall p x t, t_x_free p t x = true 
           -> Axiom_system ((∀ x , p) → (substitute_f p t x))
  | D' : forall p x q, Axiom_system ((∀ x, (p → q)) → (∀ x, p) → (∀ x, q)) 
  | E1 : forall t, Axiom_system (equality t t)
  | E2 : forall t1 t2, Axiom_system ((equality t1 t2) → (equality t2 t1))
  | E3 : forall t1 t2 t3, Axiom_system 
           ((equality t1 t2) → (equality t2 t3) → (equality t1 t3))
  | E4 : forall r v1 v2, Axiom_system 
           (equality_4 (( atomic r v1) → (atomic r v2)) _ _ v1 v2)
  | E5 : forall f v1 v2, Axiom_system 
           (equality_4 (equality (Tfun f v1) (Tfun f v2)) _ _ v1 v2)
  | C1 : forall x p, ~(x ∈ (Formula_free_Ens p)) -> Axiom_system (p → (∀ x, p))
  | C2 : forall x p, Axiom_system p -> Axiom_system (ForAll x p).

(* 证明与演绎 *)
Inductive deduce_K (Γ: Ensemble Formula) : Formula -> Prop :=
  | K0 : forall p, p ∈ Γ -> deduce_K Γ p
  | K1 : forall p, Axiom_system p -> deduce_K Γ p
  | MP : forall p q, deduce_K Γ (p → q) -> deduce_K Γ p -> deduce_K Γ q.

End Predicate_Calculus.

(* 语法蕴涵 *)
Notation " ├ p " := (deduce_K (@ Empty_set Formula) p) (at level 80).
Notation " Γ ├ p " := (deduce_K Γ p) (at level 80).
Global Hint Constructors Axiom_system deduce_K : KD.


Fact Union_l : forall Γ p, Γ ├ p -> forall A, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact Union_r : forall Γ p, Γ ├ p -> forall A, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact Union_r_A : forall A p, A ├ p -> forall Γ, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact Union_l_A : forall A p, A ├ p -> forall Γ, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact subsetprove : forall A B p, A ⊆ B -> A ├ p -> B ├ p.
Proof.
  intros A B p H H0. induction H0.
  - apply K0. apply H. auto.
  - apply K1. auto.
  - eapply MP; eauto.
Qed.

Ltac autoK :=
  match goal with
  | H: ?Γ ├ ?p |- ?Γ ∪ ?A ├ ?p => apply Union_l; auto
  | H: ?Γ ├ ?p |- ?A ∪ ?Γ ├ ?p => apply Union_r; auto
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?Γ ├ ?p , H1: ?Γ ├ ?p → ?q |- ?Γ ├ ?q => apply MP with p; autoK
  | H: ?Γ ├ ?p |- ?Γ ├ ?q → ?p => let H0 := fresh in
      assert (H0: Γ ├ p → (q → p)) by (apply K1; apply P1; constructor); autoK
  | H1: ?Γ ├ ¬?p  → ¬?q, H2: ?Γ ├ ¬?p  → ?q |- ?Γ ├ ?p =>
      assert (H0: Γ ├ (¬p → q) → ((¬p → ¬q) → p)) by 
        (apply K1; apply P3; constructor); autoK
  | |- ?Γ ├ ?x => eauto with KD sets
  | |- forall a, ?Q => intros; autoK
  end.

Ltac Single_Union :=
  match goal with 
  | |- ?Γ ∪ [?p] ├ ?q => assert(Γ ∪ [p] ├ p); autoK
  end.

Ltac later :=
  match goal with
  | |- ?Γ ├ ?q → ?p => let H0 := fresh in assert (H0: Γ ├ p) by (autoK); autoK
  end.

(* 同一律 |- p→q *)
Proposition law_identity : forall Γ p, Γ ├ p → p.
Proof. intros. assert(Γ ├ p → (p → p) → p) by autoK. autoK. Qed.
Global Hint Resolve law_identity : KD.

(* 演绎定理  *)
Theorem Deductive_Theorem : forall Γ p q, Γ ∪ [p] ├ q <-> Γ ├ p → q.
Proof.
  split; intros.
  - induction H; try (autoK; ES).
    + assert (Γ ├ p0 → p → p0); autoK.
    + destruct H; autoK.  
  - apply MP with p; autoK.
Qed.

Corollary syllogism : forall Γ p q r, Γ ∪ [p] ├ q -> Γ ∪ [q] ├ r -> Γ ∪ [p] ├ r.
Proof.
  intros. apply Deductive_Theorem in H. apply Deductive_Theorem in H0. 
  assert (Γ ∪ [p] ├ p) by autoK. pose proof (Union_l _ _ H [p]). 
  pose proof (Union_l _ _ H0 [p]). autoK.
Qed.

Corollary Syllogism : forall Γ p q r, Γ ├ (p → q) → (q → r) → (p → r).
Proof.
  intros. apply Deductive_Theorem. repeat apply -> Deductive_Theorem.
  assert (Γ ∪ [p → q] ∪ [q → r] ∪ [p] ├ p). 
    { apply Union_r_A. pose proof (K0 [p] p). apply H. apply In_singleton. }
  assert (Γ ∪ [p → q] ∪ [q → r] ∪ [p] ├ p → q).
    { apply Union_l_A. apply Union_l_A. apply Union_r_A. 
      pose proof (K0 [p → q] (p → q)). apply H0. apply In_singleton. }
  pose proof (MP _ _ _ H0 H).
  assert (Γ ∪ [p → q] ∪ [q → r] ∪ [p] ├ q → r).
    { apply Union_l_A. repeat apply Union_r_A. pose proof (K0 [q → r] (q → r)).
      apply H2. apply In_singleton. }
  pose proof (MP _ _ _ H2 H1). apply H3.
Qed.

(* 反证律 *)
Theorem rule_Indirect : forall Γ p q, Γ ∪ [¬p] ├ q ->  Γ ∪ [¬p] ├ ¬q -> Γ ├ p.
Proof. intros. apply Deductive_Theorem in H0, H. autoK. Qed.

(* 推论 双重否定律 *)
Corollary law_double_negation_aux : forall p, [¬¬p] ├ p.
Proof. intros. pose proof (rule_Indirect [¬¬p] p ¬p). apply H; autoK. Qed.
Global Hint Resolve law_double_negation_aux :KD.

Corollary law_double_negation : forall  Γ p, Γ ├ ¬¬p → p.
Proof. intros; apply Deductive_Theorem. apply Union_r_A. autoK. Qed.
Global Hint Resolve law_double_negation : KD.

(* 归谬律 *)
Theorem rule_Reduction_absurdity :
  forall Γ p q, Γ ∪[p] ├ q -> Γ ∪[p] ├ ¬q -> Γ ├ ¬p.
Proof.
  intros. assert (Γ ∪ [¬¬p] ├ q). { eapply (syllogism Γ (¬¬p) p q); autoK. } 
  assert (Γ ∪ [¬¬p] ├ ¬q). { eapply (syllogism Γ (¬¬p) p (¬q)); autoK. }
  apply (rule_Indirect _ _ _ H1 H2); auto.
Qed.

(* 第二双重否定律 *)
Corollary law_double_negation_second_aux : forall  p, [p] ├ ¬¬p.
Proof.
  intros. pose proof (rule_Reduction_absurdity [p] ¬p p). apply H; autoK.
Qed.

Corollary law_double_negation_second : forall Γ p , Γ ├ p → ¬¬p.
Proof.
  intros. pose proof (law_double_negation_second_aux p).
  assert (Γ ∪ [p] ├ ¬¬p). { apply Union_r_A. auto. }
  apply Deductive_Theorem in H0. auto.
Qed.
Global Hint Resolve law_double_negation_second : KD.

(* L3 |- (¬p → ¬q) → (q → p) *)
Fact L3 : forall Γ p q, Γ ├ ((¬p → ¬q) → (q → p)).
Proof.
  intros. apply Deductive_Theorem. apply -> Deductive_Theorem.
  apply rule_Indirect with q. eauto with *. apply MP with ¬p.
  eauto with *. eauto with *.
Qed.

(* 否定前件律 *)
Proposition law_deny_antecedent : forall Γ p q, Γ ├ ¬q → (q → p).
Proof.
  intros. assert (Γ ├ (¬p → ¬q) → (q → p)). { pose proof (L3 Γ p q). apply H. }
  assert (Γ ├ ((¬p → ¬q) → (q → p))→ (¬q → ((¬p → ¬q) → (q → p)))).
    { pose proof (P1 ((¬p → ¬q) → (q → p)) ¬q). apply K1. apply H0. }
  pose proof (MP _ _ _ H0 H).
  assert (Γ ├ (¬q → (¬p → ¬q) → (q → p)) → ((¬q → (¬p → ¬q)) → (¬q → (q → p)))).
    { pose proof (P2 ¬q (¬p → ¬q) (q → p)). apply K1. apply H2. }
  pose proof (MP _ _ _ H2 H1).
  assert (Γ ├ ¬q → (¬p → ¬q)). { pose proof (P1 ¬q ¬p). apply K1. apply H4. }
  pose proof (MP _ _ _ H3 H4). apply H5.
Qed.
Global Hint Resolve law_deny_antecedent : KD.

(* 否定肯定律 *)
Proposition law_negetion_affirmation : forall Γ p, Γ ├ (¬p → p) → p.
Proof.
  intros. apply Deductive_Theorem. set (Γ ∪ [¬p → p]) as A.
  pose proof (law_deny_antecedent A ¬(¬p → p) p).
  assert (A ├ (¬p → p → ¬(¬p → p)) → (¬p → p) → ¬p → ¬(¬p → p)).
    { pose proof (P2 ¬p p ¬(¬p → p)). apply K1. apply H0. }
  pose proof (MP _ _ _ H0 H).
  assert ( A ├ (¬p → p)). { apply Union_r_A. pose proof (K0 [¬p → p] (¬p → p)).
    apply H2. apply In_singleton. }
  pose proof (MP _ _ _ H1 H2).
  assert ( A ├ (¬p → ¬(¬p → p)) → (¬p → p) → p). 
    { pose proof (L3 A p (¬p → p)). apply H4. }
  pose proof (MP _ _ _ H4 H3). pose proof (MP _ _ _ H5 H2). apply H6.
Qed.
Global Hint Resolve law_negetion_affirmation : KD.

(* 换位律 *)
Fact law_inverse_prop : forall Γ p q, Γ ├ (q → p) → (¬p → ¬q).
Proof.
  intros. apply Deductive_Theorem. assert (Γ ∪ [q → p] ├ ¬¬q → q) by autoK.
  pose proof (K0 (Γ ∪ [q → p]) (q → p)). assert ((q → p) ∈ (Γ ∪ [q → p])) by ES.
  apply H0 in H1. pose proof (Syllogism (Γ ∪ [q → p]) ¬¬q q p).
  pose proof (MP _ _ _ H2 H). pose proof (MP _ _ _ H3 H1).
  assert (Γ ∪ [q → p] ├ p → ¬¬p). { apply law_double_negation_second. }
  pose proof (Syllogism (Γ ∪ [q → p]) ¬¬q p ¬¬p).
  pose proof (MP _ _ _ H6 H4). pose proof (MP _ _ _ H7 H5).
  assert (Γ ∪ [q → p] ├ (¬¬q → ¬¬p) → ¬p → ¬q).
  { pose proof (L3 (Γ ∪ [q → p]) ¬q ¬p). auto. }
  pose proof (MP _ _ _ H9 H8). auto.
Qed.
Global Hint Resolve law_inverse_prop : KD.

(* Peirce律 *)
Fact law_peirce : forall Γ p q , Γ ├ ((p → q) → p) → p.
Proof.
  intros. apply Deductive_Theorem. assert (Γ ├ ¬p → (p → q)) by autoK. 
  apply Union_l with (A := [(p → q) → p]) in H. Single_Union.
Qed.
Global Hint Resolve law_peirce : KD.

Proposition prop_3_6_1 : forall p q Γ, Γ ├ (p ∧ q) → p.
Proof.
  intros. pose proof (law_deny_antecedent Γ ¬q p).
  pose proof (law_inverse_prop Γ (p → ¬q) ¬p). pose proof (MP _ _ _ H0 H).
  pose proof (law_double_negation Γ p). pose proof (Syllogism Γ ¬(p → ¬q) ¬¬p p).
  pose proof (MP _ _ _ H3 H1). pose proof (MP _ _ _ H4 H2). auto.
Qed.

Proposition prop_3_6_2 : forall p q Γ, Γ ├ (p ∧ q) → q.
Proof.
  intros. assert (Γ ├ ¬q → p → ¬q) by autoK.
  pose proof (law_inverse_prop Γ (p → ¬q) ¬q). pose proof (MP _ _ _ H0 H).
  pose proof (law_double_negation Γ q). pose proof (Syllogism Γ ¬(p → ¬q) ¬¬q q).
  pose proof (MP _ _ _ H3 H1). pose proof (MP _ _ _ H4 H2). auto.
Qed.

Proposition prop_3_6_5 : forall p q Γ, Γ ├ p → (q → (p ∧ q)).
Proof.
  intros. repeat apply -> Deductive_Theorem.
  assert (Γ ∪ [p] ∪ [q] ∪ [p → ¬q] ├ q) by autoK.
  assert (Γ ∪ [p] ∪ [q] ∪ [p → ¬q] ├ ¬q). { apply MP with p; autoK. }
  apply (rule_Reduction_absurdity (Γ ∪ [p] ∪ [q]) (p → ¬q) q H H0).
Qed.

Proposition prop_3_7_1 : forall p q Γ, Γ ├ (p ↔ q) → (p → q).
Proof. intros. apply prop_3_6_1. Qed.

Proposition prop_3_7_2 : forall p q Γ, Γ ├ (p ↔ q) → (q → p).
Proof. intros. apply prop_3_6_2. Qed.

Lemma equivalent_theorem : forall p q Γ, Γ ├ (p ↔ q) <-> Γ ├ p → q /\ Γ ├ q → p.
Proof.
  intros. split.
  - intro. split.
    + apply MP with (p ↔ q). apply prop_3_7_1. auto.
    + apply MP with (p ↔ q). apply prop_3_7_2. auto.
  - intro. destruct H. specialize (prop_3_6_5 (p → q) (q → p)). 
    intros. pose proof MP _ _ _ (H1 Γ) H. apply MP with (q → p); auto.
Qed.

(* ========================================== *)
Theorem Gen_Rule : forall (x: Var) (p: Formula),
  ├ p -> ├ (∀ x, p).
Proof.
  intros. induction H. destruct H.
  - apply K1. apply C2. auto.
  - apply MP with (∀ x, p).
    apply MP with (∀ x, (p → q)). apply K1. apply D'.
    auto. auto.
Qed.

Theorem Gen_Rule_1 : forall (Γ : Ensemble Formula) (x: Var) (p: Formula),
  Γ ├ p -> ~(x ∈ (Formula_free_Ens p)) ->  Γ ├ (∀ x, p).
Proof.
  intros. assert (Γ ├ p → (∀ x, p)).
    { apply K1. apply C1. auto. }
  pose proof (MP _ _ _ H1 H). auto.
Qed.

(* 在项t中把变元x替换成自身Tvar x，项恒等 *)
Lemma subst_t_id : forall t x, substitute_t t (Tvar x) x = t.
Proof.
  fix IH 1. intros. destruct t.
  - simpl. destruct (eqbv x v) eqn:E. unfold eqbv in E. destruct x.
    destruct v; auto. apply Nat.eqb_eq in E. subst; auto. auto.
  - simpl. auto.
  - simpl. f_equal.
    Print Vector.t.
    induction t eqn:H.
    + auto.
    + f_equal.
      * apply IH.
      * eapply IHt0; eauto.
Qed.

(* 项向量替换 *)
Lemma subst_v_id : forall n (v: Vector.t term n) x,
  substitute_v n v (Tvar x) x = v.
Proof.
  induction v; simpl; auto. intros. rewrite IHv. rewrite subst_t_id. auto.
Qed.

(* 公式的恒等代换identity p[x/x] = p *)
Lemma subst_f_id : forall p x, substitute_f p (Tvar x) x = p.
Proof.
  induction p; simpl; intros; auto.
  - rewrite subst_t_id,subst_t_id. auto.
  - rewrite subst_v_id. auto.
  - rewrite IHp. auto.
  - rewrite IHp1, IHp2. auto.
  - destruct (eqbv x v); auto. rewrite IHp. auto.
Qed.

Example exam_3_1: forall (p: Formula) (x: Var), [¬∃ x, ¬p ] ├ (∀ x, p).
Proof.
  intros. assert(Step1_7: [¬∃ x, ¬p ] ├ p).
  { assert (H1: [¬∃ x, ¬p ] ├ ¬∃ x, ¬p) by (apply K0; apply In_singleton).
    unfold Exists at 2 in H1.
    assert (H2: [¬∃ x, ¬p ] ├ (¬¬(∀ x, (¬¬p))) → (∀ x, (¬¬p))).
      { apply law_double_negation. }
    assert (H3: [¬∃ x, ¬p ] ├ ∀ x, (¬¬p)). { eapply MP; eauto. }
    assert (H4: [¬∃ x, ¬p ] ├ (∀ x, (¬¬p)) → (¬¬p)).
      { pose proof (S' (¬¬p) x (Tvar x)). rewrite subst_f_id in H.
        apply K1. apply H. apply free_test_3. }
    assert (H5: [¬∃ x, ¬p ] ├ ¬¬p). { eapply MP; eauto. }
    assert (H6: [¬∃ x, ¬p ] ├ ¬¬p → p). { apply law_double_negation. }
    apply MP with (¬¬p); auto. }
  assert (H1: ├ ¬(∃ x, ¬p) → p).
    { assert(Empty_set Formula ∪ [¬(∃ x, ¬p)] ├ p). eapply Union_r_A; eauto.
      apply (Deductive_Theorem (@ Empty_set Formula) (¬(∃ x, ¬p)) p). auto. }
  assert (H2: ├ ∀ x, (¬(∃ x, ¬p) → p)). { eapply Gen_Rule. eauto. }
  assert (H3: ├ (∀ x, ((¬∃ x, ¬p) → p)) → (∀ x, ¬(∃ x, ¬p)) → (∀ x, p)).
    { apply K1. apply D'. }
  pose proof (MP _ _ _ H3 H2) as H4.
  assert (H5: [¬∃ x, ¬p] ├ ∀ x, (¬∃ x, ¬p)). { apply MP with (¬∃ x, ¬ p).
    - apply K1. apply C1.  unfold Exists. red. intro H.
      destruct H as [_ H]. elim H. apply In_singleton. 
    - apply K0. apply In_singleton. }
  apply MP with (∀ x, ¬(∃ x, ¬p)); auto.
  apply subsetprove with (A := Empty_set Formula).
  unfold Included. intros. destruct H. auto.
Qed.

Fact Union_empty_l: forall (A: Ensemble Formula), Empty_set Formula ∪ A = A.
Proof.
  intros. apply Extensionality_Ensembles. red. split.
  - red. intros. destruct H. destruct H. auto.
  - red. intros. right. auto.
Qed.

Example exam_3_2: forall (p q: Formula) (x: Var),
[∀ x, (p → q)] ∪ [∀ x, ¬q] ├ (∀ x, (¬p)).
Proof.
  intros. assert (├ (p → q) → ¬ q → ¬ p).
  { apply Deductive_Theorem. apply -> Deductive_Theorem.
    assert (Empty_set Formula ∪ [p → q] ∪ [¬q] ∪ [p] ├ ¬q) by autoK.
    assert (Empty_set Formula ∪ [p → q] ∪ [¬q] ∪ [p] ├ q).
      { assert (Empty_set Formula ∪ [p → q] ∪ [p] ├ p) by autoK.
        assert (Empty_set Formula ∪ [p → q] ∪ [p] ├ p → q) by autoK.
        pose proof (MP _ _ _ H1 H0) as H2.
        apply subsetprove with (A := Empty_set Formula ∪ [p → q] ∪ [p]).
        red. intros. destruct H3; ES. auto. }
    pose proof (rule_Reduction_absurdity 
      (Empty_set Formula ∪ [p → q] ∪ [¬q]) p q) as H1.
    apply H1 in H0. auto. auto. }
  assert (H1: ├ ∀ x, ((p → q) → ¬ q → ¬ p)). { eapply Gen_Rule. eauto. }
  assert (H2: ├ (∀ x, ((p → q) → ¬ q → ¬ p))
    → (∀ x, ((p → q)) →  (∀ x,(¬ q → ¬ p)))). { apply K1. apply D'. }
  pose proof (MP _ _ _ H2 H1). apply Deductive_Theorem in H0.
  assert (Empty_set Formula ∪ [∀ x, (p → q)] ├ (∀ x, (¬q → ¬p))
    → (∀ x, ¬q) → (∀ x, ¬p)). { apply K1. apply D'. }
  pose proof (MP _ _ _ H3 H0). apply Deductive_Theorem in H4.
  rewrite Union_empty_l in H4. auto.
Qed.

Example exam_3_3: forall (p: Formula) (x: Var), [∀ x, p] ├ (∃ x, p).
Proof.
  intros. assert ([∀ x, p] ∪ [∀ x, ¬p]├ ∀ x, ¬p) by autoK.
  assert ([∀ x, p] ∪ [∀ x, ¬p]├ ∀ x, p) by autoK.
  assert ([∀ x, p] ∪ [∀ x, ¬p]├ (∀ x, ¬p) → ¬p).
    { pose proof (S' (¬p) x (Tvar x)). rewrite subst_f_id in H1.
      apply K1. apply H1. apply free_test_3. }
  assert ([∀ x, p] ∪ [∀ x, ¬p]├ (∀ x, p) → p).
    { pose proof (S' p x (Tvar x)). rewrite subst_f_id in H2.
      apply K1. apply H2. apply free_test_3. }
  pose proof (MP _ _ _ H1 H).
  pose proof (MP _ _ _ H2 H0).
  pose proof (rule_Reduction_absurdity [∀ x, p] (∀ x, ¬p) p). 
  apply H5 in H4. apply H4. apply H3.
Qed.

Proposition prop_3_9: forall x p t, t_x_free p t x = true -> ├ p → (∃ x, p).
Proof.
  intros. assert (├ (∀ x, (¬p)) → (¬p)).
    { pose proof (S' (¬p) x (Tvar x)). rewrite subst_f_id in H0.
      apply K1. apply H0. apply free_test_3. }
  assert (├ ((∀ x, (¬p)) → (¬p)) → (p → ¬(∀ x, (¬p)))).
    { apply Deductive_Theorem. apply -> Deductive_Theorem. 
      assert (Φ ∪ [(∀ x, (¬p)) → ¬p] ∪ [p] ∪ [∀ x, (¬p)] ├ p) by autoK.
      assert (Φ ∪ [(∀ x, (¬p)) → ¬p] ∪ [p] ∪ [∀ x, (¬p)] ├ ¬p).
    { assert (Φ ∪ [(∀ x, (¬p)) → ¬p] ∪ [∀ x, (¬p)] ├ (∀ x, (¬p))) by autoK.
      assert (Φ ∪ [(∀ x, (¬p)) → ¬p] ∪ [∀ x, (¬p)] ├ (∀ x, (¬p)) → ¬p) by autoK.
      pose proof (MP _ _ _ H3 H2) as H4.
      apply subsetprove with (A := Φ ∪ [(∀ x, (¬p)) → ¬p] ∪ [∀ x, (¬p)]).
      red. intros. destruct H5; ES. auto. }
  pose proof (rule_Reduction_absurdity 
    (Φ ∪ [(∀ x, (¬p)) → ¬p] ∪ [p]) (∀ x, (¬p)) p).
  apply H3 in H2. auto. auto. }
  pose proof (MP _ _ _ H1 H0) as H2. auto.
Qed.

Proposition prop_3_10: forall (p q: Formula) (x: Var),
  ├ (∀ x, (p → q)) → ((∃ x, p) → (∃ x, q)).
Proof.
  intros.
  pose proof (exam_3_2 p q x).
  apply Deductive_Theorem in H.
  pose proof (law_inverse_prop [∀ x, (p → q)] (∀ x, ¬p) (∀ x, ¬q)).
  pose proof (MP _ _ _ H0 H). apply  Deductive_Theorem.
  rewrite Union_empty_l. auto.
Qed.

Proposition prop_3_11: forall (Γ: Ensemble Formula) (p q: Formula) (x: Var),
  Γ ∪ [p] ├ q -> ~ (x ∈ (Formula_free_Ens p))
  -> ~ (x ∈ (Formula_free_Ens q)) ->  Γ ∪ [∃ x, p] ├ q.
Proof.
  intros. apply Deductive_Theorem in H.
  pose proof (law_inverse_prop Γ q p).
  pose proof (MP _ _ _ H2 H).
  assert (Γ ├ ∀ x, (¬q → ¬p)).
    { apply Gen_Rule_1. auto. red. intro.
      simpl in H4. Search ( ?x ∈ (?A ∪ ?B)). apply UnionI in H4.
      destruct H4. destruct H1. auto. destruct H0;auto. } 
  assert (Γ ├ (∀ x, (¬q → ¬p)) → (∀ x, ¬q) → (∀ x, ¬p)).
    { apply K1. apply D'. }
  pose proof (MP _ _ _ H5 H4).
  assert (Γ ├ ((∀ x, ¬q) → (∀ x, ¬p)) → (¬(∀ x, ¬p) → ¬(∀ x, ¬q))).
    { pose proof (law_inverse_prop Γ (∀ x, ¬p) (∀ x, ¬q)). auto. }
  pose proof (MP _ _ _ H7 H6). apply Deductive_Theorem in H8.
  assert (H9: Γ ∪ [¬(∀ x, ¬p)] ├ ¬(∀ x, ¬q) → ¬¬q).
    { assert (Γ ├ ¬q → (∀ x, ¬q)). { apply K1. apply C1. simpl. auto. }
      assert (Γ ├ (¬q → (∀ x, ¬q)) → (¬(∀ x, ¬q) → ¬¬q)).
        { pose proof (law_inverse_prop Γ (∀ x, ¬q) ¬q). auto. }
      pose proof (MP _ _ _ H10 H9). apply subsetprove with (A := Γ).
      unfold Included. intros. left. auto. auto. }
  pose proof (MP _ _ _ H9 H8).
  assert (Γ ∪ [¬(∀ x, ¬p)] ├ ¬¬q → q).
    { pose proof (law_double_negation (Γ ∪ [¬(∀ x, ¬p)]) q). auto. }
  pose proof (MP _ _ _ H11 H10). auto.
Qed.

Proposition prop_3_12_1: forall p x y,
  ~(x ∈ (Formula_free_Ens p)) -> ~(y ∈ (Formula_free_Ens p))
  -> ├ (∀ x, p) → (∀ y, p).
Proof.
  intros. apply Deductive_Theorem. assert (Φ ∪ [∀ x, p] ├ ∀ x, p) by autoK.
  assert (Φ ∪ [∀ x, p] ├ (∀ x, p) → p).
    { pose proof (S' p x (Tvar x)). rewrite subst_f_id in H2.
      apply K1. apply H2. apply free_test_3. }
  pose proof (MP _ _ _ H2 H1). apply Gen_Rule_1. auto. auto.
Qed.

Proposition prop_3_12_2: forall p x y,
  ~(x ∈ (Formula_free_Ens p)) -> ~(y ∈ (Formula_free_Ens p))
  -> ├ (∃ x, p) → (∃ y, p).
Proof.
  intros. assert (├ (∀ y, ¬p) → (∀ x, ¬p)).
    { apply Deductive_Theorem. assert (Φ ∪ [∀ y, ¬p] ├ ∀ y, ¬p) by autoK.
      assert (Φ ∪ [∀ y, ¬p] ├ (∀ y, ¬p) → ¬p).
        { pose proof (S' ¬p y (Tvar y)). rewrite subst_f_id in H2.
          apply K1. apply H2. apply free_test_3. }
      pose proof (MP _ _ _ H2 H1). apply Gen_Rule_1. auto. auto. }
  assert (├ ((∀ y, ¬p) → (∀ x, ¬p)) → (¬(∀ x, ¬p) → ¬(∀ y, ¬p))).
    { apply (law_inverse_prop Φ (∀ x, ¬p) (∀ y, ¬p)). }
  pose proof (MP _ _ _ H2 H1). auto.
Qed.

Proposition prop_3_13_1: forall p x, ├ (¬(∀ x, p)) ↔ (∃ x, ¬p).
Proof.
  intros. assert(├ (∀ x, ¬¬p) → (∀ x, p)).
    { assert(├ (∀ x, ¬¬p) → (¬¬p)).
        { pose proof (S' (¬¬p) x (Tvar x)). rewrite subst_f_id in H.
          apply K1. apply H. apply free_test_3. }
      assert(├ (¬¬p) → p).
        { apply Deductive_Theorem. eapply Union_r_A.
          apply law_double_negation_aux. }
      assert(├ (∀ x, ¬¬p) → p).
        { apply Deductive_Theorem in H0. apply Deductive_Theorem in H0.
          pose proof (syllogism Φ (∀ x, ¬¬p) (¬¬p) p).
          apply Deductive_Theorem in H, H0. apply H1 in H.
          apply Deductive_Theorem. auto. auto. }
      assert (├ ∀ x, (¬¬p → p)).
        { apply Gen_Rule. apply law_double_negation. }
      assert (├ (∀ x, (¬¬p → p)) → (∀ x, ¬¬p) → (∀ x, p)).
        { apply K1. apply D'. }
      pose proof (MP _ _ _ H3 H2). auto. }
  assert(├ (∀ x, p) → (∀ x, ¬¬p)).
    { assert(├ (∀ x, p) → p).
        { pose proof (S' p x (Tvar x)). rewrite subst_f_id in H0.
          apply K1. apply H0. apply free_test_3. }
      assert(├ p → (¬¬p)).
        { apply Deductive_Theorem. eapply Union_r_A.
          apply law_double_negation_second_aux. }
      assert(├ (∀ x, p) → (¬¬p)).
        { apply Deductive_Theorem in H0. apply Deductive_Theorem in H1.
          pose proof (syllogism Φ (∀ x, p) p (¬¬p)).
          apply H2 in H0; auto. apply Deductive_Theorem. auto. }
      assert (├ ∀ x, (p → ¬¬p)).
        { apply Gen_Rule. apply law_double_negation_second. }
      assert (├ (∀ x, (p → ¬¬p)) → (∀ x, p) → (∀ x, ¬¬p)).
        { apply K1. apply D'. }
      pose proof (MP _ _ _ H4 H3). auto. }
  apply equivalent_theorem. split.
  - pose proof (law_inverse_prop Φ (∀ x, p) (∀ x, ¬¬p)).
    pose proof (MP _ _ _ H1 H). auto.
  - pose proof (law_inverse_prop Φ (∀ x, ¬¬p) (∀ x, p)).
    pose proof (MP _ _ _ H1 H0). auto.
Qed.

Proposition prop_3_13_2: forall p x, ├ (¬(∃ x, p)) ↔ (∀ x, ¬p).
Proof.
  intros. assert(├ (¬¬(∀ x, ¬p)) ↔ (∀ x, ¬p)).
    { assert(├ (¬¬(∀ x, ¬p)) → (∀ x, ¬p)) by autoK.
      assert(├ (∀ x, ¬p) → (¬¬(∀ x, ¬p))) by autoK.
      apply equivalent_theorem. eauto. }
  unfold Exists. auto.
Qed.




