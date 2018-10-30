Require Export A_2.

(* A.3 类的初等代数 *)

Module A3.

(* 定理2  并集 x∪y = {z:z∈x或者z∈y} *)

Definition Union x y : Class := \{ λ z, z∈x \/ z∈y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

Hint Unfold Union : set.


(* 定义3  交集 x∩y = {z:z∈x同时z∈y} *)

Definition Intersection x y : Class := \{ λ z, z∈x /\ z∈y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

Hint Unfold Intersection : set.


(* 定理4  z∈x∪y当且仅当z∈x或者z∈y，而z∈x∩y当且仅当z∈x同时z∈y *)

Theorem Theorem4 : forall (x y: Class) (z: Class),
  z∈x \/ z∈y <-> z ∈ (x ∪ y).
Proof.
  intros.
  split; intros.
  - apply AxiomII; split.
    + destruct H; Ens.
    + apply H.
  - apply AxiomII in H.
    apply H.
Qed.

Theorem Theorem4' : forall x y z, z∈x /\ z∈y <-> z∈(x∩y).
Proof.
  intros; unfold Intersection; split; intros.
  - apply AxiomII; split; Ens; exists y; apply H.
  - apply AxiomII in H; apply H.
Qed.

Hint Resolve Theorem4 Theorem4' : set.


(* 定理5  x∪x=x同时x∩x=x *)

Theorem Theorem5 : forall x, x ∪ x = x.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4 in H; tauto.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem5' : forall x, x ∩ x = x.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H; tauto.
  - apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem5 Theorem5' : set.


(* 定理6  x∪y=y∪x同时x∩y=y∩x *)

Theorem Theorem6 : forall x y, x ∪ y = y ∪ x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4 in H; apply Theorem4; tauto.
  - apply Theorem4 in H; apply Theorem4; tauto.
Qed.

Theorem Theorem6' : forall x y, x ∩ y = y ∩ x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4' in H; apply Theorem4'; tauto.
  - apply Theorem4' in H; apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem6 Theorem6' : set.


(* 定理7  (x∪y)∪z=x∪(y∪z)同时(x∩y)∩z=x∩(y∩z) *)

Theorem Theorem7 : forall x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; apply AxiomI; split; intro.
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
  intros; apply AxiomI; split; intro.
  - repeat (apply Theorem4' in H; destruct H).
    apply Theorem4'; split; auto; apply Theorem4'; auto.
  - apply Theorem4' in H; destruct H; apply Theorem4'.
    apply Theorem4' in H0; destruct H0; split; auto.
    apply Theorem4'; split; auto.
Qed.

Hint Rewrite Theorem7 Theorem7' : set.


(* 定理8  x∩(y∪z)=(x∩y)∪(x∩z)同时x∪(y∩z)=(x∪y)∩(x∪z) *)

Theorem Theorem8 : forall x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply AxiomI; split; intros.
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
  intros; apply AxiomI; split; intro.
  - apply Theorem4'; apply Theorem4 in H.
    destruct H; split; try apply Theorem4; auto.
    + apply Theorem4' in H; tauto.
    + apply Theorem4' in H; tauto.
  - apply Theorem4; apply Theorem4' in H; destruct H.
    apply Theorem4 in H; apply Theorem4 in H0.
    destruct H, H0; auto; right; apply Theorem4'; auto.
Qed.

Hint Rewrite Theorem8 Theorem8' : set.


(* 定义9  x∉y当且仅当x∈y不真 *)

Definition NotIn x y : Prop := ~ x∈y.

Notation "x ∉ y" := (NotIn x y) (at level 10).

Hint Unfold NotIn : set.


(* 定义10  ¬x={y：y∉x} *)

Definition Complement x : Class := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

Hint Unfold Complement : set.


(* 定理11  ¬ (¬ x) = x *)

Theorem Theorem11: forall x, ¬ (¬ x) = x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply AxiomII in H; unfold NotIn in H; destruct H.
    assert (z ∈ ¬ x <-> Ensemble z /\ z∉x ).
    { split; intros.
      - apply AxiomII in H1; auto.
      - apply AxiomII; auto. }
    apply definition_not in H1; auto.
    apply not_and_or in H1; destruct H1; tauto.
  - apply AxiomII; split; Ens; unfold NotIn; intro.
    apply AxiomII in H0; destruct H0; contradiction.
Qed.

Hint Rewrite Theorem11 : set.


(* 定理12  De Morgan   ¬(x∪y)=(¬x)∩(¬y)同时¬(x∩y)=(¬x)∪(¬y) *)

Theorem Theorem12 : forall x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; generalize (Theorem4 x y); intros.
  apply AxiomI; split; intros.
  - apply AxiomII in H0; destruct H0; unfold NotIn in H1.
    apply definition_not with (B:= z∈x \/ z∈y ) in H1.
    + apply not_or_and in H1; apply Theorem4'; split.
      * apply AxiomII; split; auto; unfold NotIn; tauto.
      * apply AxiomII; split; auto; unfold NotIn; tauto.
    + split; apply H.
  - apply Theorem4' in H0; destruct H0.
    apply AxiomII in H0; apply AxiomII in H1.
    apply AxiomII; split; try tauto.
    destruct H0, H1; unfold NotIn in H2,H3; unfold NotIn.
    apply definition_not with (A:= z∈x \/ z∈y ); auto.
    apply and_not_or; split; auto.
Qed.

Theorem Theorem12' : forall x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros; generalize (Theorem4' x y); intros.
  apply AxiomI; split; intro.
  - apply AxiomII in H0; unfold NotIn in H0; destruct H0.
    apply definition_not with (B:= z∈x /\ z∈y) in H1.
    + apply Theorem4; apply not_and_or in H1; destruct H1.
      * left; apply AxiomII; split; auto.
      * right; apply AxiomII; split; auto.
    + split; apply H.
  - apply AxiomII; split; Ens.
    unfold NotIn; apply definition_not with (A:= z∈x /\ z∈y); auto.
    apply or_not_and; apply Theorem4 in H0; destruct H0.
    + apply AxiomII in H0; unfold NotIn in H0; tauto.
    + apply AxiomII in H0; unfold NotIn in H0; tauto.
Qed.

Hint Rewrite Theorem12 Theorem12' : set.


(* 定义13  x~y=x∩(¬ y) *)

Definition Setminus x y : Class := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

Hint Unfold Setminus : set.


(* 定理14  x∩(y~z)=(x∩y)~z *)

Theorem Theorem14 : forall x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Setminus; rewrite Theorem7'; auto.
Qed.

Hint Rewrite Theorem14 : set.


(* 定义85  x≠y 当且仅当 x=y 不真 *)

Definition Inequality (x y: Class) : Prop := ~ (x = y).

Notation "x ≠ y" := (Inequality x y) (at level 70).

Corollary Property_Ineq : forall x y, (x ≠ y) <-> (y ≠ x).
Proof.
 intros; split; intros; intro; apply H; auto.
Qed.

Hint Unfold Inequality: set.
Hint Resolve Property_Ineq: set.


(* 定义15  Φ={x:x≠x} *)

Definition Φ : Class := \{λ x, x ≠ x \}.

Hint Unfold Φ : set.


(* 定理16  x∉Φ *)

Theorem Theorem16 : forall x, x ∉ Φ.
Proof.
  intros; unfold NotIn; intro.
  apply AxiomII in H; destruct H; contradiction.
Qed.

Hint Resolve Theorem16 : set. 


(* 定理17  Φ∪x=x同时Φ∩x=Φ *)

Theorem Theorem17 : forall x, Φ ∪ x = x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    generalize (Theorem16 z); contradiction.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem17' : forall x, Φ ∩ x = Φ.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4' in H; destruct H; auto.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem17 Theorem17' : set.


(* 定义18  全域 μ={x:x=x} *)

Definition μ : Class := \{ λ x, x = x \}.

Corollary Property_μ : forall x, x ∪ (¬ x) = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII; split; Ens.
  - apply AxiomII in H; destruct H; apply Theorem4.
    generalize (classic (z∈x)); intros; destruct H1; try tauto.
    right; apply AxiomII; split; auto.
Qed.

Hint Unfold μ : set.
Hint Rewrite Property_μ : set.


(* 定理19  x∈μ当且仅当x是一个集  *)

Theorem Theorem19 : forall x, x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intro.
  - apply AxiomII in H; destruct H; tauto.
  - apply AxiomII; split; auto.
Qed.

Hint Resolve Theorem19 : set.


(* 定理20  x∪μ=μ同时x∩μ=x *)

Theorem Theorem20 : forall x, x ∪ μ = μ.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    apply Theorem19; Ens.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem20' : forall x, x ∩ μ = x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4' in H; tauto.
  - apply Theorem4'; split; auto.
    apply Theorem19; Ens.
Qed.

Hint Rewrite Theorem20 Theorem20' : set.


(* 定理21  ¬Φ=μ同时¬μ=Φ *) 

Theorem Theorem21 : ¬ Φ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem19; Ens.
  - apply Theorem19 in H; apply AxiomII; split; auto.
    apply Theorem16; auto.
Qed.

Theorem Theorem21' : ¬ μ = Φ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H; destruct H.
    apply Theorem19 in H; contradiction.
  - apply AxiomII in H; destruct H; contradiction.
Qed.

Hint Rewrite Theorem21 Theorem21' : set.


(* 定义22  ∩x={z:对于每个y，如果y∈x，则z∈y} *) 

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

Hint Unfold Element_I : set.


(* 定义23  ∪x={z:对于某个y，z∈y同时y∈x} *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

Hint Unfold Element_U : set.


(* 定理24  ∩Φ=μ同时∪Φ=Φ *)

Theorem Theorem24 : ∩ Φ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem19; Ens.
  - apply AxiomII; apply Theorem19 in H; split; auto.
    intros; generalize (Theorem16 y); contradiction.
Qed.

Theorem Theorem24' : ∪ Φ = Φ.
Proof.
  intros; apply AxiomI; split; intro.
  - apply AxiomII in H; destruct H, H0, H0.
    generalize (Theorem16 x); contradiction.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem24 Theorem24' : set. 


(* 定义25  x⊂y 当且仅当对于每个z，如果z∈x，则z∈y *)

Definition Included x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Included x y) (at level 70).

Hint Unfold Included : set.


(* 定理26  Φ⊂x同时x⊂μ *)

Theorem Theorem26 : forall x, Φ ⊂ x.
Proof.
  intros; unfold Included; intros.
  generalize (Theorem16 z); contradiction.
Qed.

Theorem Theorem26' : forall x, x ⊂ μ.
Proof.
  intros; unfold Included; intros; apply Theorem19; Ens.
Qed.

Hint Resolve Theorem26 Theorem26' : set.


(* 定理27  x=y当且仅当x⊂y同时y⊂x *)

Theorem Theorem27 : forall x y, (x ⊂ y /\ y ⊂ x) <-> x=y.
Proof.
  intros; split; intros.
  - destruct H; intros; apply AxiomI; split; auto.
  - rewrite <- H; split; unfold Included; auto.
Qed.

Hint Resolve Theorem27 : set.


(* 定理28  如果x⊂y且y⊂z，则x⊂z *)

Theorem Theorem28 : forall x y z, x ⊂ y /\ y ⊂ z -> x ⊂ z.
Proof.
  intros; destruct H; unfold Included; auto.
Qed.

Hint Resolve Theorem28 : set.


(* 定理29  x⊂y当且仅当x∪y=y *)

Theorem Theorem29 : forall x y, x ∪ y = y <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Included; intros; apply AxiomI with (z:=z) in H.
    apply H; apply Theorem4; tauto.
  - apply AxiomI; split; intros.
    + apply Theorem4 in H0; destruct H0; auto.
    + apply Theorem4; tauto.
Qed.

Hint Resolve Theorem29 : set.


(* 定理30  x⊂y当且仅当x∩y=x *)

Theorem Theorem30 : forall x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Included; intros; apply AxiomI with (z:=z) in H.
    apply H in H0; apply Theorem4' in H0; tauto.
  - apply AxiomI; split; intros.
    + apply Theorem4' in H0; tauto.
    + apply Theorem4'; split; auto.
Qed.

Hint Resolve Theorem30 : set.


(* 定理31  如果x⊂y,则∪x⊂∪y同时∩y⊂∩x *)

Theorem Theorem31 : forall x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros; split.
  - unfold Included; intros; apply AxiomII in H0; destruct H0.
    apply AxiomII; split; auto; intros; destruct H1.
    exists x0; split; unfold Included in H; destruct H1; auto.
  - unfold Included in H; unfold Included; intros.
    apply AxiomII in H0; destruct H0; apply AxiomII; split; auto.
Qed.

Hint Resolve Theorem31 : set.


(* 定理32  如果x∈y,则x⊂∪y同时∩y⊂x *)

Theorem Theorem32 : forall x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros; split.
  - unfold Included; intros; apply AxiomII; split; Ens.
  - unfold Included; intros; apply AxiomII in H0.
    destruct H0; apply H1; auto.
Qed.

Hint Resolve Theorem32 : set.


(* Proper Subset *)

Definition ProperSubset x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperSubset x y) (at level 70).

Corollary Property_ProperSubset : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperSubset; auto.
Qed.

Corollary Property_ProperSubset' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperSubset in H; destruct H.
  generalize (Theorem27 x y); intros.
  apply definition_not with (B:= (x ⊂ y /\ y ⊂ x)) in H0; try tauto.
  apply not_and_or in H0; destruct H0; try tauto.
  unfold Included in H0; apply not_all_ex_not in H0; destruct H0.
  apply imply_to_and in H0; Ens.
Qed.

Hint Unfold ProperSubset : set.
Hint Resolve Property_ProperSubset Property_ProperSubset' : set.


(* Property_Φ *)

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperSubset in H; destruct H; auto.
    apply Property_ProperSubset' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Setminus; apply Theorem4'; split; auto.
      unfold Complement; apply AxiomII; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply AxiomI; split; intros.
    + unfold Setminus in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply AxiomII in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.

Hint Resolve Property_Φ : set.


End A3.

Export A3.
