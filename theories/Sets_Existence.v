Require Export Elementary_Algebra.

(* EXISTENCE OF SETS *)

Module Existence.

(* III Axiom of subsets  If x is a set there is a set y such that for each z,
   if z⊂x, then z∈y. *)

Axiom Axiom_Subsets : forall (x: Class),
  Ensemble x -> exists y, Ensemble y /\ (forall z, z⊂x -> z∈y).

Hint Resolve Axiom_Subsets : set.


(* 33 Theorem  If x is a set and z⊂x, then z is a set. *)

Theorem Theorem33 : forall x z,
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros; apply Axiom_Subsets in H; destruct H.
  apply H in H0; Ens.
Qed.

Hint Resolve Theorem33 : set.


(* 34 Theorem  Φ = ∩μ and ∪μ = μ. *)

Theorem Theorem34 : Φ = ∩μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - generalize (Theorem16 z); contradiction.
  - apply Axiom_Scheme in H; destruct H; apply H0.
    apply Theorem19; generalize (Theorem26 z); intros.
    apply Theorem33 in H1; auto.
Qed.

Theorem Theorem34' : μ = ∪μ.
Proof.
  apply Axiom_Extent; split; intros.
  - apply Lemma_x in H; destruct H; apply Axiom_Scheme in H.
    destruct H; apply Axiom_Scheme; split; try auto.
    generalize (Axiom_Subsets z H); intros.
    destruct H2; destruct H2; exists x; split.
    + apply H3; unfold Subclass; auto.
    + apply Theorem19; auto.
  - apply Axiom_Scheme in H; destruct H; apply Theorem19; auto.
Qed.

Hint Rewrite Theorem34 Theorem34' : set.


(* 35 Theorem  If x ≠ Φ, then ∩x is a set. *)

Lemma Lemma35 : forall x, x ≠ Φ <-> exists z, z∈x.
Proof.
  intros; assert (x = Φ <-> ~ (exists y, y∈x)).
  { split; intros.
    - intro; destruct H0; rewrite H in H0.
      apply Axiom_Scheme in H0; destruct H0; case H1; auto.
    - apply Axiom_Extent; split; intros.
      + elim H; exists z; auto.
      + generalize (Theorem16 z); contradiction. }
  split; intros.
  - apply definition_not with (B:= ~(exists y, y∈x)) in H0; auto.
    apply NNPP in H0; destruct H0; exists x0; auto.
  - apply definition_not with (A:=(~ (exists y, y∈x))); auto.
    destruct H; split; auto.
Qed.

Theorem Theorem35 : forall x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros; apply Lemma35 in H; destruct H; AssE x0.
  generalize (Theorem32 x0 x H); intros.
  destruct H1; apply Theorem33 in H2; auto.
Qed.

Hint Resolve Lemma35 Theorem35 : set.


(* 36 Definition  pow(x) = { y : y ⊂ x }. *)

Definition PowerClass x : Class := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerClass x) (at level 0, right associativity).

Hint Unfold PowerClass : set.


(* 37 Theorem  μ = pow(μ). *)

Theorem Theorem37 : μ = pow(μ).
Proof.
  apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; split; Ens; apply Theorem26'.
  - apply Axiom_Scheme in H; destruct H; apply Theorem19; auto.
Qed.

Hint Rewrite Theorem37 : set.


(* 38 Theorem  If x is a set, then pow(x) is a set, and for each y, y ⊂ x iff
   y ∈ pow(x). *)

Theorem Theorem38 : forall x y,
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros; split.
  - apply Axiom_Subsets in H; destruct H, H.
    assert (pow(x) ⊂ x0).
    { unfold Subclass; intros; apply Axiom_Scheme in H1.
      destruct H1; apply H0 in H2; auto. }
    apply Theorem33 in H1; auto.
  - split; intros.
    + apply Theorem33 with (z:=y) in H; auto.
      apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme in H0; apply H0.
Qed.

Hint Resolve Theorem38 : set.


(* 39 Theorem  μ is not a set. *)

(* Russell paradox *)

Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  generalize (classic (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \})).
  intros; destruct H.
  - double H; apply Axiom_Scheme in H; destruct H; contradiction.
  - intro; elim H; apply Axiom_Scheme; split; auto.
Qed.

Theorem Theorem39 : ~ Ensemble μ.
Proof.
  unfold not; generalize Lemma_N; intros.
  generalize (Theorem26' \{ λ x, x ∉ x \}); intros.
  apply Theorem33 in H1; auto.
Qed.

Hint Resolve Lemma_N Theorem39 : set.


(* 40 Definition  [x] = { z : if x∈μ, then z=x }. *)

Definition Singleton x : Class := \{ λ z, x∈μ -> z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Hint Unfold Singleton : set.


(* 41 Theorem  If x is a set, for each y, y∈[x] iff y=x. *)

Theorem Theorem41 : forall x, Ensemble x -> (forall y, y∈[x] <-> y=x).
Proof.
  intros; split; intros.
  - apply Axiom_Scheme in H0; destruct H0; apply H1.
    apply Theorem19 in H; auto.
  - apply Axiom_Scheme; split; intros; auto.
    rewrite <- H0 in H; auto.
Qed.

Hint Resolve Theorem41 : set.


(* 42 Theorem  If x is a set, then [x] is a set. *)

Theorem Theorem42 : forall x, Ensemble x -> Ensemble [x].
Proof.
  intros; double H; apply Theorem33 with (x:= pow(x)).
  - apply Theorem38 with (y:=x) in H0; destruct H0; auto.
  - unfold Subclass; intros.
    apply Theorem38 with (y:=z) in H0; destruct H0.
    apply H2; apply Axiom_Scheme in H1; destruct H1.
    apply Theorem19 in H; apply H3 in H.
    rewrite H; unfold Subclass; auto.
Qed.

Hint Resolve Theorem42 : set.


(* 43 Theorem  [x] = μ if and only if x is not a set. *)

Theorem Theorem43 : forall x, [x] = μ <-> ~ Ensemble x.
Proof.
  split; intros.
  - unfold not; intros; apply Theorem42 in H0.
    rewrite H in H0; generalize Theorem39; contradiction.
  - generalize (Theorem19 x); intros.
    apply definition_not with (B:= x∈μ) in H; try tauto.
    apply Axiom_Extent; split; intros.
    * apply Axiom_Scheme in H1; destruct H1; apply Theorem19; auto.
    * apply Axiom_Scheme; split; try contradiction.
      apply Theorem19 in H1; auto.
Qed.

Hint Rewrite Theorem43 : set.


(* 42' Theorem  If [x] is a set, then x is a set. *)

Theorem Theorem42' : forall x, Ensemble [x] -> Ensemble x.
Proof.
  intros.
  generalize (classic (Ensemble x)); intros.
  destruct H0; auto; generalize (Theorem39); intros.
  apply Theorem43 in H0; auto.
  rewrite H0 in H; contradiction.
Qed.

Hint Resolve Theorem42' : set.


(* 44 Theorem  If x is a set, then ∩[x] = x and ∪[x] = x; if x is not a set,
   then ∩[x] = Φ and ∪[x] = μ. *)

Theorem Theorem44 : forall x, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  intros; generalize (Theorem41 x H); intros.
  split; apply Axiom_Extent.
  - split; intros.
    + apply Axiom_Scheme in H1; destruct H1; apply H2; apply H0; auto.
    + apply Axiom_Scheme; split; Ens; intros.
      apply H0 in H2; rewrite H2; auto.
  - split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2, H2.
      unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
      rewrite H4 in H2; auto; apply Theorem19; auto.
    + apply Axiom_Scheme; split; Ens; exists x; split; auto.
      unfold Singleton; apply Axiom_Scheme; auto.
Qed.

Theorem Theorem44' : forall x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros; apply Theorem43 in H; split; rewrite H.
  - rewrite Theorem34; auto.
  - rewrite <- Theorem34'; auto.
Qed.

Hint Resolve Theorem44 Theorem44' : set.


(* IV Axiom of union  If x is a set and y is a set so is x∪y. *)

Axiom Axiom_Union : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble (x∪y).

Corollary Axiom_Union': forall x y,
  Ensemble (x∪y) -> Ensemble x /\ Ensemble y.
Proof.
  intros; split.
  - assert (x ⊂ (x∪y)).
    { unfold Subclass; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
  - assert (y ⊂ (x∪y)).
    { unfold Subclass; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
Qed.

Hint Resolve Axiom_Union Axiom_Union' : set.


(* 45 Definition  [x|y] = [x] ∪ [y]. *)

Definition Unordered x y : Class := [x]∪[y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

Hint Unfold Unordered : set.


(* 46 Theorem  If x is a set and y is a set, then [x|y] is a set and z∈[x|y]
   iff z=x or z=y; [x|y] = μ iff x is not a set or y is not a set. *)

Theorem Theorem46 : forall x y z,
  Ensemble x /\ Ensemble y -> Ensemble [x|y] /\ (z∈[x|y] <-> (z=x \/ z=y)).
Proof.
  split; intros; destruct H.
  - apply Theorem42 in H; apply Theorem42 in H0; apply Axiom_Union; auto.
  - split; intros.
    + apply Axiom_Scheme in H1; destruct H1.
      destruct H2; apply Axiom_Scheme in H2; destruct H2.
      * left; apply H3; apply Theorem19; auto.
      * right; apply H3; apply Theorem19; auto.
    + apply Axiom_Scheme; split.
      * destruct H1; try rewrite <- H1 in H; auto.
        rewrite <- H1 in H0; auto.
      * destruct H1.
        -- left; apply Axiom_Scheme; split; rewrite <- H1 in H; auto.
        -- right; apply Axiom_Scheme; split; rewrite <- H1 in H0; auto.
Qed.

Theorem Theorem46' : forall x y, [x|y] = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  unfold Unordered; split; intros.
  - generalize (Theorem43 ([x] ∪ [y])); intros.
    destruct H0; rewrite H in H0.
    assert ([μ] = μ); try apply Theorem43; try apply Theorem39.
    apply H0 in H2; rewrite <- H in H2.
    assert (Ensemble([x]∪[y]) <-> Ensemble [x] /\ Ensemble [y]).
    { split; try apply Axiom_Union; try apply Axiom_Union'. }
    apply definition_not in H3; auto.
    generalize (not_and_or (Ensemble [x]) (Ensemble [y])); intros.
    apply H4 in H3; destruct H3.
    + assert (Ensemble [x] <-> Ensemble x).
      { split; try apply Theorem42'; try apply Theorem42; auto. }
      apply definition_not in H5; auto.
    + assert (Ensemble [y] <-> Ensemble y).
      { split; try apply Theorem42'; try apply Theorem42; auto. }
      apply definition_not in H5; auto.
  - destruct H; apply Theorem43 in H; rewrite H; try apply Theorem20.
    generalize (Theorem6 μ [y]); intros; rewrite H0; apply Theorem20.
Qed.

Hint Resolve Theorem46 Theorem46' : set.


(* 47 Theorem  If x and y are sets, then ∩[x|y] = x ∩ y and ∪[x|y] = x ∪ y;
   if either x or y is not a set, then ∩[x|y] = Φ and ∪[x|y] = μ. *)

Theorem Theorem47 : forall x y,
  Ensemble x /\ Ensemble y -> (∩[x|y] = x ∩ y) /\ (∪[x|y] = x ∪ y).
Proof.
  intros; split; apply Axiom_Extent; intros.
  - split; intros.
    + apply Theorem4'.
      split; apply Axiom_Scheme in H0; destruct H0; apply H1; apply Theorem4.
      * left; apply Axiom_Scheme; split; try apply H; auto.
      * right; apply Axiom_Scheme; split; try apply H; auto.
    + apply Theorem4' in H0; destruct H0.
      apply Axiom_Scheme; split; intros; try AssE z.
      apply Theorem4 in H2; destruct H2.
      * apply Axiom_Scheme in H2; destruct H2; destruct H.
        apply Theorem19 in H; apply H4 in H; rewrite H; auto.
      * apply Axiom_Scheme in H2; destruct H2; destruct H.
        apply Theorem19 in H5; apply H4 in H5; rewrite H5; auto.
  - split; intros.
    + apply Axiom_Scheme in H0; destruct H0; destruct H1; destruct H1.
      apply Theorem4 in H2; apply Theorem4.
      destruct H2; apply Axiom_Scheme in H2; destruct H2.
      * left; destruct H; apply Theorem19 in H.
        apply H3 in H; rewrite H in H1; auto.
      * right; destruct H; apply Theorem19 in H4.
        apply H3 in H4; rewrite H4 in H1; auto.
    + apply Theorem4 in H0; apply Axiom_Scheme.
      split; destruct H0; try AssE z.
      * exists x; split; auto; apply Theorem4; left.
        apply Axiom_Scheme; split; try apply H; trivial.
      * exists y; split; auto; apply Theorem4; right.
        apply Axiom_Scheme; split; try apply H; trivial.
Qed.

Theorem Theorem47' : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> (∩[x|y] = Φ) /\ (∪[x|y] = μ).
Proof.
  intros; split; apply Theorem46' in H; rewrite H.
  - rewrite Theorem34; auto.
  - rewrite <- Theorem34'; auto.
Qed.

Hint Resolve Theorem47 Theorem47' : set.


End Existence.

Export Existence.