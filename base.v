Require Export Coq.Sets.Ensembles.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a) (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).

Corollary UnionI : forall {U} (a:U) B C, a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. split; intros; destruct H; eauto with sets. Qed.

Corollary Single : forall {U} (a x:U), a ∈ [ x ] <-> a = x.
Proof. split; intros; destruct H; auto. apply In_singleton. Qed.

Global Hint Resolve UnionI Single: sets.
