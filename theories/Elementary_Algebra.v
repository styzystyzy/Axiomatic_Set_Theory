Require Export Classification_Axiom_Scheme.

(* ELEMENTARY ALGEBRA OF CLASSES *)

Module Algebra.

(* 2 Definition  x∪y = { z : z∈x or z∈y }. *)

Definition Union x y : Class := \{ λ z, z∈x \/ z∈y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

Hint Unfold Union : set.


(* 3 Definition  x∩y = { z : z∈x and z∈y }. *)

Definition Intersection x y : Class := \{ λ z, z∈x /\ z∈y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

Hint Unfold Intersection : set.


(* 4 Theorem  z∈x∪y if and only if z∈x or z∈y, and z∈x∩y if and only if
   z∈x and z∈y. *)

Theorem bel_union : forall (x y: Class) (z: Class),
  z∈x \/ z∈y <-> z ∈ (x ∪ y).
Proof.
  intros.
  split; intros.
  - apply Axiom_Scheme; split.
    + destruct H; Ens.
    + apply H.
  - apply Axiom_Scheme in H.
    apply H.
Qed.

Theorem bel_inter : forall x y z, z∈x /\ z∈y <-> z∈(x∩y).
Proof.
  intros; unfold Intersection; split; intros.
  - apply Axiom_Scheme; split; Ens; exists y; apply H.
  - apply Axiom_Scheme in H; apply H.
Qed.

Hint Resolve bel_union bel_inter : set.


(* 5 Theorem  x∪x=x and x∩x=x. *)

Theorem union_fix : forall x, x ∪ x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply bel_union in H; tauto.
  - apply bel_union; tauto.
Qed.

Theorem inter_fix : forall x, x ∩ x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply bel_inter in H; tauto.
  - apply bel_inter; tauto.
Qed.

Hint Rewrite union_fix inter_fix : set.


(* 6 Theorem  x∪y=y∪x and x∩y=y∩x. *)

Theorem union_com : forall x y, x ∪ y = y ∪ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_union in H; apply bel_union; tauto.
  - apply bel_union in H; apply bel_union; tauto.
Qed.

Theorem inter_com : forall x y, x ∩ y = y ∩ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_inter in H; apply bel_inter; tauto.
  - apply bel_inter in H; apply bel_inter; tauto.
Qed.

Hint Rewrite union_com inter_com : set.


(* 7 Theorem  (x∪y)∪z=x∪(y∪z) and (x∩y)∩z=x∩(y∩z). *)

Theorem union_ass : forall x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_union in H; apply bel_union; destruct H.
    + apply bel_union in H; destruct H; try tauto.
      right; apply bel_union; auto.
    + right; apply bel_union; auto.
  - apply bel_union in H; apply bel_union; destruct H.
    + left; apply bel_union; auto.
    + apply bel_union in H; destruct H; try tauto.
      left; apply bel_union; tauto.
Qed.

Theorem inter_ass : forall x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - repeat (apply bel_inter in H; destruct H).
    apply bel_inter; split; auto; apply bel_inter; auto.
  - apply bel_inter in H; destruct H; apply bel_inter.
    apply bel_inter in H0; destruct H0; split; auto.
    apply bel_inter; split; auto.
Qed.

Hint Rewrite union_ass inter_ass : set.


(* 8 Theorem  x∩(y∪z)=(x∩y)∪(x∩z) and x∪(y∩z)=(x∪y)∩(x∪z). *)

Theorem union_dist : forall x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply bel_union; apply bel_inter in H; destruct H.
    apply bel_union in H0; destruct H0.
    + left; apply bel_inter; split; auto.
    + right; apply bel_inter; split; auto.
  - apply bel_union in H; apply bel_inter; destruct H.
    + apply bel_inter in H; destruct H; split; auto.
      apply bel_union; left; auto.
    + apply bel_inter in H; destruct H; split; auto.
      apply bel_union; right; auto.
Qed.


Theorem inter_dist : forall x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_inter; apply bel_union in H.
    destruct H; split; try apply bel_union; auto.
    + apply bel_inter in H; tauto.
    + apply bel_inter in H; tauto.
  - apply bel_union; apply bel_inter in H; destruct H.
    apply bel_union in H; apply bel_union in H0.
    destruct H, H0; auto; right; apply bel_inter; auto.
Qed.

Hint Rewrite union_dist inter_dist : set.


(* 9 Definition  x∉y if and only if it is false that x∈y. *)

Definition NotIn x y : Prop := ~ x∈y.

Notation "x ∉ y" := (NotIn x y) (at level 10).

Hint Unfold NotIn : set.


(* 10 Definition  ¬x = { y : y ∉ x }. *)

Definition Complement x : Class := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

Hint Unfold Complement : set.


(* 11 Theorem  ¬ (¬ x) = x *)

Theorem comp_fix: forall x, ¬ (¬ x) = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H; unfold NotIn in H; destruct H.
    assert (z ∈ ¬ x <-> Ensemble z /\ z∉x ).
    { split; intros.
      - apply Axiom_Scheme in H1; auto.
      - apply Axiom_Scheme; auto. }
    apply definition_not in H1; auto.
    apply not_and_or in H1; destruct H1; tauto.
  - apply Axiom_Scheme; split; Ens; unfold NotIn; intro.
    apply Axiom_Scheme in H0; destruct H0; contradiction.
Qed.

Hint Rewrite comp_fix : set.


(* 12 Theorem (De Morgan)  ¬(x∪y)=(¬x)∩(¬y) and ¬(x∩y)=(¬x)∪(¬y). *)

Theorem demorgan_union : forall x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; generalize (bel_union x y); intros.
  apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0; unfold NotIn in H1.
    apply definition_not with (B:= z∈x \/ z∈y ) in H1.
    + apply not_or_and in H1; apply bel_inter; split.
      * apply Axiom_Scheme; split; auto; unfold NotIn; tauto.
      * apply Axiom_Scheme; split; auto; unfold NotIn; tauto.
    + split; apply H.
  - apply bel_inter in H0; destruct H0.
    apply Axiom_Scheme in H0; apply Axiom_Scheme in H1.
    apply Axiom_Scheme; split; try tauto.
    destruct H0, H1; unfold NotIn in H2,H3; unfold NotIn.
    apply definition_not with (A:= z∈x \/ z∈y ); auto.
    apply and_not_or; split; auto.
Qed.

Theorem demorgan_inter : forall x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros; generalize (bel_inter x y); intros.
  apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H0; unfold NotIn in H0; destruct H0.
    apply definition_not with (B:= z∈x /\ z∈y) in H1.
    + apply bel_union; apply not_and_or in H1; destruct H1.
      * left; apply Axiom_Scheme; split; auto.
      * right; apply Axiom_Scheme; split; auto.
    + split; apply H.
  - apply Axiom_Scheme; split; Ens.
    unfold NotIn; apply definition_not with (A:= z∈x /\ z∈y); auto.
    apply or_not_and; apply bel_union in H0; destruct H0.
    + apply Axiom_Scheme in H0; unfold NotIn in H0; tauto.
    + apply Axiom_Scheme in H0; unfold NotIn in H0; tauto.
Qed.

Hint Rewrite demorgan_union demorgan_inter : set.


(* 13 Definition  x~y = x ∩ (¬ y). *)

Definition Difference x y : Class := x ∩ (¬ y).

Notation "x ~ y" := (Difference x y) (at level 50, left associativity).

Hint Unfold Difference : set.


(* 14 Theorem  x ∩ (y~z) = (x∩y) ~ z. *)

Theorem inter_diff : forall x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Difference; rewrite inter_ass; auto.
Qed.

Hint Rewrite inter_diff : set.


(* Definition (85)  x≠y if and only if it is false that x=y. *)

Definition Inequality (x y: Class) : Prop := ~ (x = y).

Notation "x ≠ y" := (Inequality x y) (at level 70).

Corollary Property_Ineq : forall x y, (x ≠ y) <-> (y ≠ x).
Proof.
 intros; split; intros; intro; apply H; auto.
Qed.

Hint Unfold Inequality: set.
Hint Resolve Property_Ineq: set.


(* 15 Definition  Φ = { x : x ≠ x }. *)

Definition Φ : Class := \{λ x, x ≠ x \}.

Hint Unfold Φ : set.


(* 16 Theorem  x ∉ Φ. *)

Theorem not_bel_zero : forall x, x ∉ Φ.
Proof.
  intros; unfold NotIn; intro.
  apply Axiom_Scheme in H; destruct H; contradiction.
Qed.

Hint Resolve not_bel_zero : set. 


(* 17 Theorem  Φ ∪ x = x and Φ ∩ x = Φ. *)

Theorem zero_union : forall x, Φ ∪ x = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_union in H; destruct H; try tauto.
    generalize (not_bel_zero z); contradiction.
  - apply bel_union; tauto.
Qed.

Theorem zero_inter : forall x, Φ ∩ x = Φ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_inter in H; destruct H; auto.
  - generalize (not_bel_zero z); contradiction.
Qed.

Hint Rewrite zero_union zero_inter : set.


(* 18 Definition  μ = { x : x = x }. *)

Definition μ : Class := \{ λ x, x = x \}.

Corollary Property_μ : forall x, x ∪ (¬ x) = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; split; Ens.
  - apply Axiom_Scheme in H; destruct H; apply bel_union.
    generalize (classic (z∈x)); intros; destruct H1; try tauto.
    right; apply Axiom_Scheme; split; auto.
Qed.

Hint Unfold μ : set.
Hint Rewrite Property_μ : set.


(* 19 Theorem  x∈μ if and only if x is a set.  *)

Theorem bel_universe_set : forall x, x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intro.
  - apply Axiom_Scheme in H; destruct H; tauto.
  - apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve bel_universe_set : set.


(* 20 Theorem  x ∪ μ = μ and x ∩ μ = x. *)

Theorem universe_union : forall x, x ∪ μ = μ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_union in H; destruct H; try tauto.
    apply bel_universe_set; Ens.
  - apply bel_union; tauto.
Qed.

Theorem universe_inter : forall x, x ∩ μ = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply bel_inter in H; tauto.
  - apply bel_inter; split; auto.
    apply bel_universe_set; Ens.
Qed.

Hint Rewrite universe_union universe_inter : set.


(* 21 Theorem  ¬ Φ = μ and ¬ μ = Φ. *)

Theorem zero_comp_universe : ¬ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply bel_universe_set; Ens.
  - apply bel_universe_set in H; apply Axiom_Scheme; split; auto.
    apply not_bel_zero; auto.
Qed.

Theorem universe_comp_zero : ¬ μ = Φ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H.
    apply bel_universe_set in H; contradiction.
  - apply Axiom_Scheme in H; destruct H; contradiction.
Qed.

Hint Rewrite zero_comp_universe universe_comp_zero : set.


(* 22 Definition  ∩x = { z : for each y, if y∈x, then z∈y }. *)

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

Hint Unfold Element_I : set.


(* 23 Definition  ∪x = { z : for some y, z∈y and y∈x }. *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

Hint Unfold Element_U : set.


(* 24 Theorem  ∩Φ = μ and ∪Φ = Φ. *)

Theorem zero_eleI_universe : ∩ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply bel_universe_set; Ens.
  - apply Axiom_Scheme; apply bel_universe_set in H; split; auto.
    intros; generalize (not_bel_zero y); contradiction.
Qed.

Theorem zero_eleU_zero : ∪ Φ = Φ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H; destruct H, H0, H0.
    generalize (not_bel_zero x); contradiction.
  - generalize (not_bel_zero z); contradiction.
Qed.

Hint Rewrite zero_eleI_universe zero_eleU_zero : set. 


(* 25 Definition  x ⊂ y iff for each z, if z∈x, then z∈y. *)

Definition Subclass x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Subclass x y) (at level 70).

Hint Unfold Subclass : set.


(* 26 Theorem  Φ ⊂ x and x ⊂ μ. *)

Theorem zero_sub : forall x, Φ ⊂ x.
Proof.
  intros; unfold Subclass; intros.
  generalize (not_bel_zero z); contradiction.
Qed.

Theorem sub_universe : forall x, x ⊂ μ.
Proof.
  intros; unfold Subclass; intros; apply bel_universe_set; Ens.
Qed.

Hint Resolve zero_sub sub_universe : set.


(* 27 Theorem  x=y iff x⊂y and y⊂x. *)

Theorem sub_eq : forall x y, (x ⊂ y /\ y ⊂ x) <-> x=y.
Proof.
  intros; split; intros.
  - destruct H; intros; apply Axiom_Extent; split; auto.
  - rewrite <- H; split; unfold Subclass; auto.
Qed.

Hint Resolve sub_eq : set.


(* 28 Theorem  If x⊂y and y⊂z, then x⊂z. *)

Theorem sub_tran : forall x y z, x ⊂ y /\ y ⊂ z -> x ⊂ z.
Proof.
  intros; destruct H; unfold Subclass; auto.
Qed.

Hint Resolve sub_tran : set.


(* 29 Theorem  x⊂y iff x∪y = y. *)

Theorem union_sub : forall x y, x ∪ y = y <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros; apply Axiom_Extent with (z:=z) in H.
    apply H; apply bel_union; tauto.
  - apply Axiom_Extent; split; intros.
    + apply bel_union in H0; destruct H0; auto.
    + apply bel_union; tauto.
Qed.

Hint Resolve union_sub : set.


(* 30 Theorem  x⊂y iff x∩y = x. *)

Theorem inter_sub : forall x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros; apply Axiom_Extent with (z:=z) in H.
    apply H in H0; apply bel_inter in H0; tauto.
  - apply Axiom_Extent; split; intros.
    + apply bel_inter in H0; tauto.
    + apply bel_inter; split; auto.
Qed.

Hint Resolve inter_sub : set.


(* 31 Theorem  If x ⊂ y, then ∪x ⊂ ∪y and ∩y ⊂ ∩x. *)

Theorem sub_ele : forall x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros; split.
  - unfold Subclass; intros; apply Axiom_Scheme in H0; destruct H0.
    apply Axiom_Scheme; split; auto; intros; destruct H1.
    exists x0; split; unfold Subclass in H; destruct H1; auto.
  - unfold Subclass in H; unfold Subclass; intros.
    apply Axiom_Scheme in H0; destruct H0; apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve sub_ele : set.


(* 32 Theorem  If x∈y, then x ⊂ ∪y and ∩y ⊂ x. *)

Theorem bel_ele : forall x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros; split.
  - unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
  - unfold Subclass; intros; apply Axiom_Scheme in H0.
    destruct H0; apply H1; auto.
Qed.

Hint Resolve bel_ele : set.


(* Proper Subclass *)

Definition ProperSubclass x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperSubclass x y) (at level 70).

Corollary Property_ProperSubclass : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperSubclass; auto.
Qed.

Corollary Property_ProperSubclass' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperSubclass in H; destruct H.
  generalize (sub_eq x y); intros.
  apply definition_not with (B:= (x ⊂ y /\ y ⊂ x)) in H0; try tauto.
  apply not_and_or in H0; destruct H0; try tauto.
  unfold Subclass in H0; apply not_all_ex_not in H0; destruct H0.
  apply imply_to_and in H0; Ens.
Qed.

Hint Unfold ProperSubclass : set.
Hint Resolve Property_ProperSubclass Property_ProperSubclass' : set.


(* Property_Φ *)

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperSubclass in H; destruct H; auto.
    apply Property_ProperSubclass' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Difference; apply bel_inter; split; auto.
      unfold Complement; apply Axiom_Scheme; split; Ens. }
    rewrite H0 in H2; generalize (not_bel_zero z); intros.
    contradiction.
  - rewrite <- H0; apply Axiom_Extent; split; intros.
    + unfold Difference in H1; apply bel_inter in H1.
      destruct H1; unfold Complement in H2.
      apply Axiom_Scheme in H2; destruct H2; contradiction.
    + generalize (not_bel_zero z); intros; contradiction.
Qed.

Hint Resolve Property_Φ : set.


End Algebra.

Export Algebra.

