Require Export Sets_Existence.

(* ORDERED PAIRS: RELATIONS *)

Module OrderedP.

(* 48 Definition  [x,y] = [[x]|[x|y]] *)

Definition Ordered x y : Class := [ [x] | [x|y]].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

Hint Unfold Ordered : set.


(* 49 Theorem  [x,y] is a set if and only if x is a set and y is a set;
   if [x,y] is not a set, then [x,y] = μ. *)

Theorem Theorem49 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble x /\ Ensemble y.
Proof.
  intros; split; intro.
  - unfold Ordered in H; unfold Unordered in H.
    apply Axiom_Union' in H; destruct H; apply Theorem42' in H.
    apply Theorem42' in H; apply Theorem42' in H0; split; auto.
    unfold Unordered in H0; apply Axiom_Union' in H0.
    destruct H0; apply Theorem42' in H1; auto.
  - destruct H; unfold Ordered, Unordered; apply Axiom_Union; split.
    + apply Theorem42; auto; apply Theorem42; auto.
    + apply Theorem42; auto; apply Theorem46; auto.
Qed.

Theorem Theorem49' : forall (x y: Class),
  ~ Ensemble [x,y] -> [x,y] = μ.
Proof.
  intros; generalize (Theorem49 x y); intros.
  apply definition_not with (B:= Ensemble x /\ Ensemble y) in H; try tauto.
  apply not_and_or in H; apply Theorem46' in H; auto.
  generalize Theorem39; intros; rewrite <-H in H1.
  unfold Ordered; apply Theorem46'; auto.
Qed.

Hint Resolve Theorem49 Theorem49' : set.


(* 50 Theorem  If x and y are sets, then ∪[x,y]=[x|y], ∩[x,y]=[x], ∪∩[x,y]=x,
   ∩∩[x,y]=x, ∪∪[x,y]=x∪y, ∩∪[x,y]=x∩y. If either x or y is not a set,
   then ∪∩[x,y]=Φ, ∩∩[x,y]=Φ, ∪∪[x,y]=Φ, ∩∪[x,y]=Φ. *)

Lemma Lemma50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x] /\ Ensemble [x | y].
Proof.
  intros; apply Theorem49 in H; auto.
  unfold Ordered in H; unfold Unordered in H.
  apply Axiom_Union' in H; destruct H.
  apply Theorem42' in H; auto.
  apply Theorem42' in H0; auto.
Qed.

Theorem Theorem50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\
  (∪(∩[x,y]) = x) /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  intros; elim H; intros.
  repeat unfold Ordered; apply Lemma50 in H.
  apply Theorem47 in H; auto; elim H; intros; repeat split.
  - rewrite H3; apply Axiom_Extent; split; intros; try (apply Theorem4; tauto).
    apply Theorem4 in H4; destruct H4; auto; apply Theorem4; tauto.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Theorem4' in H4; apply H4.
    + apply Theorem4'; split; auto; apply Theorem4; tauto.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4, H5, H5. 
      apply Theorem4' in H6; destruct H6; apply Axiom_Scheme in H6.
      destruct H6; rewrite <- H8; auto.
      apply Theorem19; auto.
    + apply Axiom_Scheme; split; Ens; exists x. 
      split; auto; apply Theorem4'; split.
      * apply Axiom_Scheme; split; auto.
      * apply Theorem4; left; apply Axiom_Scheme.
        split; try apply H0; trivial.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4.
      apply H5; apply Theorem4'; split.
      * apply Axiom_Scheme; split; auto.
      * apply Theorem4; left; apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme; split; Ens.
      intros; apply Theorem4' in H5. destruct H5. 
      apply Axiom_Scheme in H5. destruct H5. rewrite H7; auto. 
      apply Theorem19; auto.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Theorem4; apply Axiom_Scheme in H4; destruct H4, H5, H5. 
      apply Theorem4 in H6; destruct H6.
      * apply Axiom_Scheme in H6; destruct H6; left; rewrite <- H7; auto. 
        apply Theorem19; auto.
      * apply Theorem4 in H6; destruct H6. 
        -- apply Axiom_Scheme in H6; destruct H6.
           left; rewrite <- H7; auto; apply Theorem19; auto.
        -- apply Axiom_Scheme in H6; destruct H6.
           right; rewrite <- H7; auto; apply Theorem19; auto.
    + apply Axiom_Scheme; apply Theorem4 in H4; split.
      * unfold Ensemble; destruct H4; Ens.
      * destruct H4.
        -- exists x; split; auto; apply Theorem4; left.
           apply Axiom_Scheme; split; auto.
        -- exists y; split; auto; apply Theorem4; right.
           apply Theorem4; right; apply Axiom_Scheme; split; auto.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Lemma_x in H4; elim H4; intros.
      apply Axiom_Scheme in H5; apply Axiom_Scheme in H6.
      destruct H4; apply Theorem4'; split; auto.
      * apply H5; apply Theorem4; left.
        apply Axiom_Scheme; split; auto.
      * apply H6; apply Theorem4; right.
        apply Theorem4; right.
        apply Axiom_Scheme; split; auto.
    + apply Theorem4' in H4; destruct H4. 
      apply Axiom_Scheme; split; Ens.
      intros; apply Theorem4 in H6; destruct H6.
      * apply Axiom_Scheme in H6; destruct H6; rewrite H7; auto.
        apply Theorem19; auto.
      * apply Axiom_Scheme in H6; destruct H6, H7.
        -- apply Axiom_Scheme in H7; destruct H7. 
           rewrite H8; auto; apply Theorem19; auto.
        -- apply Axiom_Scheme in H7; destruct H7.
           rewrite H8; auto; apply Theorem19; auto.
Qed.

Lemma Lemma50' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> ~Ensemble [x] \/ ~Ensemble [x | y].
Proof.
  intros; elim H; intros. 
  - left; apply Theorem43 in H0; auto.
    rewrite H0; apply Theorem39; auto.
  - right; apply Theorem46' in H; auto.
    rewrite H; apply Theorem39; auto.
Qed.

Theorem Theorem50' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ)
  /\ (∪(∪[x,y]) = μ) /\ (∩(∪[x,y]) = Φ).
Proof.
  intros; apply Lemma50' in H; auto.
  apply Theorem47' in H; destruct H.
  repeat unfold Ordered; repeat split.
  - rewrite H; apply Theorem24'; auto.
  - rewrite H; apply Theorem24; auto.
  - rewrite H0; rewrite <- Theorem34'; auto.
  - rewrite H0; rewrite <- Theorem34; auto.
Qed.

Hint Resolve Theorem50 Theorem50' : set.


(* 51 Definition  1st coord z = ∩∩z. *)

Definition First z := ∩∩z.

Hint Unfold First : set.


(* 52 Definition  2nd coord z = (∩∪z)∪(∪∪z)~(∪∩z). *)

Definition Second z := (∩∪z)∪(∪∪z)~(∪∩z).

Hint Unfold Second : set.


(* 53 Theorem  2nd coord μ = μ. *)

Lemma Lemma53 : μ ~ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; destruct H; auto.
  - apply Theorem4'; split; auto.
    apply Axiom_Scheme; split.
    * apply Theorem19 in H; auto.
    * apply Theorem16; auto.
Qed.

Theorem Theorem53 : Second μ = μ.
Proof.
  intros; unfold Second.
  repeat rewrite <-Theorem34'; auto.
  repeat rewrite <-Theorem34 ; auto.
  rewrite Theorem24'; auto.
  rewrite Lemma53; auto.
  apply Theorem20; auto.
Qed.

Hint Rewrite Theorem53 : set.


(* 54 Theorem  If x and y are sets, 1st coord [x,y] = x and 2nd coord [x,y] = y.
   If either of x and y is not a set, then 1st coord [x,y] = μ and
   2nd coord [x,y] = μ. *)

Lemma Lemma54 : forall (x y: Class),
  (x ∪ y) ~ x = y ~ x.
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; apply Theorem4 in H; split; auto.
    destruct H; auto; apply Axiom_Scheme in H0.
    destruct H0; elim H1; auto.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; split; auto.
    apply Theorem4; tauto.
Qed.

Theorem Theorem54 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> First [x,y] = x /\ Second [x,y] = y.
Proof.
  intros; apply Theorem50 in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1, H2, H3; unfold Second.
    rewrite H4; rewrite H3; rewrite H1.
    rewrite Lemma54; auto; unfold Difference.
    rewrite Theorem6'; auto; rewrite <- Theorem8; auto.
    rewrite Property_μ; auto; rewrite Theorem20'; auto.
Qed.


Theorem Theorem54' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> First [x,y] = μ /\ Second [x,y] = μ.
Proof.
  intros; apply Theorem50' in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1; unfold Second.
    rewrite H2; rewrite H1; rewrite H.
    rewrite Lemma53; auto.
    apply Theorem20; auto.
Qed.

Hint Resolve Theorem54 Theorem54' : set.


(* 55 Theorem  If x and y are sets and [x,y] = [u,v], then x=u and y=v. *)

Theorem Theorem55 : forall (x y u v: Class),
  Ensemble x /\ Ensemble y -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  intros; split; intros.
  - double H; apply Theorem49 in H; apply Theorem54 in H1; destruct H1.
    rewrite H0 in H, H1, H2; apply Theorem49 in H; apply Theorem54 in H.
    destruct H; rewrite H1 in H; rewrite H2 in H3; split; auto.
  - destruct H0; rewrite H0, H1; auto.
Qed.

Hint Resolve Theorem55 : set.


(* 56 Definition  r is a relation if and only if for each member z of r there
   is x and y such that z = [x,y]. *)

Definition Relation r : Prop :=
  forall z, z∈r -> exists x y, z = [x,y].

Hint Unfold Relation: set.


(* II Classification axiom-scheme  For each b, b ∈ { a : A } if and only if
   b is a set and B. *)

(* { [x,y] : ... }  If the member is a ordered pair, then { [x,y] : ... } is
   used. The definition of { [x,y] : ... } is to avoid excessive notation. We
   agree that { [x,y] : ... } is to be identical with { u : for some x, some y,
   u = (x,y) and ... }. *)

Parameter Classifier_P : (Class -> Class -> Prop) -> Class.

Notation "\{\ P \}\" := (Classifier_P P) (at level 0).

Axiom Axiom_SchemeP : forall (a b: Class) (P: Class -> Class -> Prop),
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).

Axiom Property_P : forall (z: Class) (P: Class -> Class -> Prop),
  z ∈ \{\ P \}\ -> (exists a b, z = [a,b]) /\ z ∈ \{\ P \}\.

Ltac PP H a b := apply Property_P in H; destruct H as [[a [b H]]];
  rewrite H in *.

Hint Resolve Axiom_SchemeP Property_P : set.


(* 57 Definition  r ∘ s = { [x,z] : for some y, [x,y]∈s and [y,z]∈r }. *)

Definition Composition r s : Class :=
 \{\ λ x z, exists y, [x,y]∈s /\ [y,z]∈r \}\.

Notation "r ∘ s" := (Composition r s) (at level 50, no associativity).

(* r∘s = {u : for some x, some y and some z, u=[x,z], [x,y]∈s and [y,z]∈r}. *)

Definition Composition' r s : Class :=
  \{ λ u, exists x y z, u = [x,z] /\ [x,y] ∈ s /\ [y,z] ∈ r \}.

Hint Unfold Composition Composition' : set.


(* 58 Theorem  (r∘s)∘t = r∘(s∘t). *)

Theorem Theorem58 : forall (r s t: Class),
  (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H a b. apply Axiom_SchemeP in H0; destruct H0, H1 as [y H1], H1.
    apply Axiom_SchemeP in H2; destruct H2, H3, H3.
    apply Axiom_SchemeP; split; auto.
    exists x; split; try tauto; apply Axiom_SchemeP; split; Ens.
    AssE [a,y]; AssE [y,x]; apply Theorem49 in H5; apply Theorem49 in H6.
    destruct H5, H6; apply Theorem49; auto.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0, H1 as [y H1], H1.
    apply Axiom_SchemeP in H1; destruct H1, H3, H3.
    apply Axiom_SchemeP; split; auto.
    exists x; split; auto; apply Axiom_SchemeP; split; Ens.
    AssE [a,x]; AssE [y,b]; apply Theorem49 in H5; apply Theorem49 in H6.
    destruct H5, H6; apply Theorem49; Ens.
Qed.

Hint Rewrite Theorem58 : set.


(* 59 Theorem  r∘(s∪t) = r∘s ∪ r∘t and r∘(s∩t) ⊂ r∘s ∩ r∘t. *)

Theorem Theorem59 : forall (r s t: Class),
  Relation r /\ Relation s -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t) /\ 
  r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  intros; split.
  - apply Axiom_Extent; split; intros.
    + PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
      apply Theorem4.
      destruct H2 as [y H2]; destruct H2.
      apply Theorem4 in H2; destruct H2.
      * left; apply Axiom_SchemeP; split; auto.
        exists y; split; auto.
      * right; apply Axiom_SchemeP; split; auto.
        exists y; split; auto.
    + apply Theorem4 in H0; destruct H0; PP H0 a b; apply Axiom_SchemeP.
      * apply Axiom_SchemeP in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply Theorem4; try tauto.
      * apply Axiom_SchemeP in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply Theorem4; try tauto.
  - unfold Subclass; intros; PP H0 a b.
    apply Axiom_SchemeP in H1; destruct H1.
    destruct H2 as [y H2]; destruct H2.
    apply Theorem4' in H2; apply Theorem4'; split.
    + apply Axiom_SchemeP; split; auto.
      exists y; split; try apply H2; auto.
    + apply Axiom_SchemeP; split; auto.
      exists y; split; try apply H2; auto.
Qed.

Hint Resolve Theorem59 : set.


(* 60 Definition  r⁻¹ = { [x,y] : [y,x] ∈ r }. *)

Definition Inverse r : Class := \{\ λ x y, [y,x]∈r \}\.

Notation "r ⁻¹" := (Inverse r)(at level 5).

Hint Unfold Inverse : set.


(* 61 Theorem  If r is a relation, then (r⁻¹)⁻¹ = r. *)

Lemma Lemma61 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble [y,x].
Proof.
  intros; split; intros.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
Qed.

Theorem Theorem61 : forall (r: Class),
  Relation r -> (r ⁻¹)⁻¹ = r.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
    apply Axiom_SchemeP in H2; apply H2.
  - unfold Relation in H; double H0; apply H in H1.
    destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply Axiom_SchemeP; split; Ens; apply Axiom_SchemeP; split; auto.
    apply Lemma61; auto; Ens.
Qed.

Hint Rewrite Theorem61 : set.


(* 62 Theorem  (r∘s)⁻¹ = (s⁻¹) ∘ (r⁻¹). *)

Theorem Theorem62 : forall (r s: Class),
  (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0 as [H0 H1].
    apply Axiom_SchemeP; split; auto.
    apply Axiom_SchemeP in H1; destruct H1, H2, H2.
    exists x; split.
    + apply Axiom_SchemeP; split; auto. 
      apply Lemma61; Ens; exists r; auto.
    + apply Axiom_SchemeP; split; auto.
      apply Lemma61; Ens.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0, H1, H1.
    apply Axiom_SchemeP; split; auto.
    apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    apply Axiom_SchemeP; split.
    + apply Lemma61; auto.
    + exists x; split; try apply H0; try apply H2.
      destruct H1; auto.
Qed.

Hint Rewrite Theorem62 : set.


End OrderedP.

Export OrderedP.

