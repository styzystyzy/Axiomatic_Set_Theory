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

Theorem Theorem4 : forall (x y: Class) (z: Class),
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

Theorem Theorem4' : forall x y z, z∈x /\ z∈y <-> z∈(x∩y).
Proof.
  intros; unfold Intersection; split; intros.
  - apply Axiom_Scheme; split; Ens; exists y; apply H.
  - apply Axiom_Scheme in H; apply H.
Qed.

Hint Resolve Theorem4 Theorem4' : set.


(* 5 Theorem  x∪x=x and x∩x=x. *)

Theorem Theorem5 : forall x, x ∪ x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4 in H; tauto.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem5' : forall x, x ∩ x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; tauto.
  - apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem5 Theorem5' : set.


(* 6 Theorem  x∪y=y∪x and x∩y=y∩x. *)

Theorem Theorem6 : forall x y, x ∪ y = y ∪ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; apply Theorem4; tauto.
  - apply Theorem4 in H; apply Theorem4; tauto.
Qed.

Theorem Theorem6' : forall x y, x ∩ y = y ∩ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; apply Theorem4'; tauto.
  - apply Theorem4' in H; apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem6 Theorem6' : set.


(* 7 Theorem  (x∪y)∪z=x∪(y∪z) and (x∩y)∩z=x∩(y∩z). *)

Theorem Theorem7 : forall x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; apply Theorem4; destruct H.
    + apply Theorem4 in H; destruct H; try tauto.
      right; apply Theorem4; auto.
    + right; apply Theorem4; auto.
  - apply Theorem4 in H; apply Theorem4; destruct H.
    + left; apply Theorem4; auto.
    + apply Theorem4 in H; destruct H; try tauto.
      left; apply Theorem4; tauto.
Qed.

Theorem Theorem7' : forall x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - repeat (apply Theorem4' in H; destruct H).
    apply Theorem4'; split; auto; apply Theorem4'; auto.
  - apply Theorem4' in H; destruct H; apply Theorem4'.
    apply Theorem4' in H0; destruct H0; split; auto.
    apply Theorem4'; split; auto.
Qed.

Hint Rewrite Theorem7 Theorem7' : set.


(* 8 Theorem  x∩(y∪z)=(x∩y)∪(x∩z) and x∪(y∩z)=(x∪y)∩(x∪z). *)

Theorem Theorem8 : forall x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4; apply Theorem4' in H; destruct H.
    apply Theorem4 in H0; destruct H0.
    + left; apply Theorem4'; split; auto.
    + right; apply Theorem4'; split; auto.
  - apply Theorem4 in H; apply Theorem4'; destruct H.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; left; auto.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; right; auto.
Qed.


Theorem Theorem8' : forall x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4'; apply Theorem4 in H.
    destruct H; split; try apply Theorem4; auto.
    + apply Theorem4' in H; tauto.
    + apply Theorem4' in H; tauto.
  - apply Theorem4; apply Theorem4' in H; destruct H.
    apply Theorem4 in H; apply Theorem4 in H0.
    destruct H, H0; auto; right; apply Theorem4'; auto.
Qed.

Hint Rewrite Theorem8 Theorem8' : set.


(* 9 Definition  x∉y if and only if it is false that x∈y. *)

Definition NotIn x y : Prop := ~ x∈y.

Notation "x ∉ y" := (NotIn x y) (at level 10).

Hint Unfold NotIn : set.


(* 10 Definition  ¬x = { y : y ∉ x }. *)

Definition Complement x : Class := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

Hint Unfold Complement : set.


(* 11 Theorem  ¬ (¬ x) = x *)

Theorem Theorem11: forall x, ¬ (¬ x) = x.
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

Hint Rewrite Theorem11 : set.


(* 12 Theorem (De Morgan)  ¬(x∪y)=(¬x)∩(¬y) and ¬(x∩y)=(¬x)∪(¬y). *)

Theorem Theorem12 : forall x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; generalize (Theorem4 x y); intros.
  apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0; unfold NotIn in H1.
    apply definition_not with (B:= z∈x \/ z∈y ) in H1.
    + apply not_or_and in H1; apply Theorem4'; split.
      * apply Axiom_Scheme; split; auto; unfold NotIn; tauto.
      * apply Axiom_Scheme; split; auto; unfold NotIn; tauto.
    + split; apply H.
  - apply Theorem4' in H0; destruct H0.
    apply Axiom_Scheme in H0; apply Axiom_Scheme in H1.
    apply Axiom_Scheme; split; try tauto.
    destruct H0, H1; unfold NotIn in H2,H3; unfold NotIn.
    apply definition_not with (A:= z∈x \/ z∈y ); auto.
    apply and_not_or; split; auto.
Qed.

Theorem Theorem12' : forall x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros; generalize (Theorem4' x y); intros.
  apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H0; unfold NotIn in H0; destruct H0.
    apply definition_not with (B:= z∈x /\ z∈y) in H1.
    + apply Theorem4; apply not_and_or in H1; destruct H1.
      * left; apply Axiom_Scheme; split; auto.
      * right; apply Axiom_Scheme; split; auto.
    + split; apply H.
  - apply Axiom_Scheme; split; Ens.
    unfold NotIn; apply definition_not with (A:= z∈x /\ z∈y); auto.
    apply or_not_and; apply Theorem4 in H0; destruct H0.
    + apply Axiom_Scheme in H0; unfold NotIn in H0; tauto.
    + apply Axiom_Scheme in H0; unfold NotIn in H0; tauto.
Qed.

Hint Rewrite Theorem12 Theorem12' : set.


(* 13 Definition  x~y = x ∩ (¬ y). *)

Definition Difference x y : Class := x ∩ (¬ y).

Notation "x ~ y" := (Difference x y) (at level 50, left associativity).

Hint Unfold Difference : set.


(* 14 Theorem  x ∩ (y~z) = (x∩y) ~ z. *)

Theorem Theorem14 : forall x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Difference; rewrite Theorem7'; auto.
Qed.

Hint Rewrite Theorem14 : set.


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

Theorem Theorem16 : forall x, x ∉ Φ.
Proof.
  intros; unfold NotIn; intro.
  apply Axiom_Scheme in H; destruct H; contradiction.
Qed.

Hint Resolve Theorem16 : set. 


(* 17 Theorem  Φ ∪ x = x and Φ ∩ x = Φ. *)

Theorem Theorem17 : forall x, Φ ∪ x = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    generalize (Theorem16 z); contradiction.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem17' : forall x, Φ ∩ x = Φ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; destruct H; auto.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem17 Theorem17' : set.


(* 18 Definition  μ = { x : x = x }. *)

Definition μ : Class := \{ λ x, x = x \}.

Corollary Property_μ : forall x, x ∪ (¬ x) = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; split; Ens.
  - apply Axiom_Scheme in H; destruct H; apply Theorem4.
    generalize (classic (z∈x)); intros; destruct H1; try tauto.
    right; apply Axiom_Scheme; split; auto.
Qed.

Hint Unfold μ : set.
Hint Rewrite Property_μ : set.


(* 19 Theorem  x∈μ if and only if x is a set.  *)

Theorem Theorem19 : forall x, x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intro.
  - apply Axiom_Scheme in H; destruct H; tauto.
  - apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem19 : set.


(* 20 Theorem  x ∪ μ = μ and x ∩ μ = x. *)

Theorem Theorem20 : forall x, x ∪ μ = μ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    apply Theorem19; Ens.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem20' : forall x, x ∩ μ = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; tauto.
  - apply Theorem4'; split; auto.
    apply Theorem19; Ens.
Qed.

Hint Rewrite Theorem20 Theorem20' : set.


(* 21 Theorem  ¬ Φ = μ and ¬ μ = Φ. *)

Theorem Theorem21 : ¬ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem19; Ens.
  - apply Theorem19 in H; apply Axiom_Scheme; split; auto.
    apply Theorem16; auto.
Qed.

Theorem Theorem21' : ¬ μ = Φ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H.
    apply Theorem19 in H; contradiction.
  - apply Axiom_Scheme in H; destruct H; contradiction.
Qed.

Hint Rewrite Theorem21 Theorem21' : set.


(* 22 Definition  ∩x = { z : for each y, if y∈x, then z∈y }. *)

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

Hint Unfold Element_I : set.


(* 23 Definition  ∪x = { z : for some y, z∈y and y∈x }. *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

Hint Unfold Element_U : set.


(* 24 Theorem  ∩Φ = μ and ∪Φ = Φ. *)

Theorem Theorem24 : ∩ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem19; Ens.
  - apply Axiom_Scheme; apply Theorem19 in H; split; auto.
    intros; generalize (Theorem16 y); contradiction.
Qed.

Theorem Theorem24' : ∪ Φ = Φ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H; destruct H, H0, H0.
    generalize (Theorem16 x); contradiction.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem24 Theorem24' : set. 


(* 25 Definition  x ⊂ y iff for each z, if z∈x, then z∈y. *)

Definition Subclass x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Subclass x y) (at level 70).

Hint Unfold Subclass : set.


(* 26 Theorem  Φ ⊂ x and x ⊂ μ. *)

Theorem Theorem26 : forall x, Φ ⊂ x.
Proof.
  intros; unfold Subclass; intros.
  generalize (Theorem16 z); contradiction.
Qed.

Theorem Theorem26' : forall x, x ⊂ μ.
Proof.
  intros; unfold Subclass; intros; apply Theorem19; Ens.
Qed.

Hint Resolve Theorem26 Theorem26' : set.


(* 27 Theorem  x=y iff x⊂y and y⊂x. *)

Theorem Theorem27 : forall x y, (x ⊂ y /\ y ⊂ x) <-> x=y.
Proof.
  intros; split; intros.
  - destruct H; intros; apply Axiom_Extent; split; auto.
  - rewrite <- H; split; unfold Subclass; auto.
Qed.

Hint Resolve Theorem27 : set.


(* 28 Theorem  If x⊂y and y⊂z, then x⊂z. *)

Theorem Theorem28 : forall x y z, x ⊂ y /\ y ⊂ z -> x ⊂ z.
Proof.
  intros; destruct H; unfold Subclass; auto.
Qed.

Hint Resolve Theorem28 : set.


(* 29 Theorem  x⊂y iff x∪y = y. *)

Theorem Theorem29 : forall x y, x ∪ y = y <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros; apply Axiom_Extent with (z:=z) in H.
    apply H; apply Theorem4; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Theorem4 in H0; destruct H0; auto.
    + apply Theorem4; tauto.
Qed.

Hint Resolve Theorem29 : set.


(* 30 Theorem  x⊂y iff x∩y = x. *)

Theorem Theorem30 : forall x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros; apply Axiom_Extent with (z:=z) in H.
    apply H in H0; apply Theorem4' in H0; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Theorem4' in H0; tauto.
    + apply Theorem4'; split; auto.
Qed.

Hint Resolve Theorem30 : set.


(* 31 Theorem  If x ⊂ y, then ∪x ⊂ ∪y and ∩y ⊂ ∩x. *)

Theorem Theorem31 : forall x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros; split.
  - unfold Subclass; intros; apply Axiom_Scheme in H0; destruct H0.
    apply Axiom_Scheme; split; auto; intros; destruct H1.
    exists x0; split; unfold Subclass in H; destruct H1; auto.
  - unfold Subclass in H; unfold Subclass; intros.
    apply Axiom_Scheme in H0; destruct H0; apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem31 : set.


(* 32 Theorem  If x∈y, then x ⊂ ∪y and ∩y ⊂ x. *)

Theorem Theorem32 : forall x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros; split.
  - unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
  - unfold Subclass; intros; apply Axiom_Scheme in H0.
    destruct H0; apply H1; auto.
Qed.

Hint Resolve Theorem32 : set.


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
  generalize (Theorem27 x y); intros.
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
    { unfold Difference; apply Theorem4'; split; auto.
      unfold Complement; apply Axiom_Scheme; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply Axiom_Extent; split; intros.
    + unfold Difference in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply Axiom_Scheme in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.

Hint Resolve Property_Φ : set.


End Algebra.

Export Algebra.

