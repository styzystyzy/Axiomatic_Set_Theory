Require Export Sets_Existence.

(* ORDERED PAIRS: RELATIONS *)

Module OrderedP.

(* 48 Definition  [x,y] = [[x]|[x|y]] *)

Definition Ordered x y : Class := [ [x] | [x|y]].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

Hint Unfold Ordered : set.


(* 49 Theorem  [x,y] is a set if and only if x is a set and y is a set;
   if [x,y] is not a set, then [x,y] = μ. *)

Theorem ord_set : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble x /\ Ensemble y.
Proof.
  intros; split; intro.
  - unfold Ordered in H; unfold Unordered in H.
    apply Axiom_Union' in H; destruct H; apply sing_set_inv in H.
    apply sing_set_inv in H; apply sing_set_inv in H0; split; auto.
    unfold Unordered in H0; apply Axiom_Union' in H0.
    destruct H0; apply sing_set_inv in H1; auto.
  - destruct H; unfold Ordered, Unordered; apply Axiom_Union; split.
    + apply sing_set; auto; apply sing_set; auto.
    + apply sing_set; auto; apply unord_set; auto.
Qed.

Theorem ord_set' : forall (x y: Class),
  ~ Ensemble [x,y] -> [x,y] = μ.
Proof.
  intros; generalize (ord_set x y); intros.
  apply definition_not with (B:= Ensemble x /\ Ensemble y) in H; try tauto.
  apply not_and_or in H; apply unord_notset in H; auto.
  generalize universe_notset; intros; rewrite <-H in H1.
  unfold Ordered; apply unord_notset; auto.
Qed.

Hint Resolve ord_set ord_set' : set.


(* 50 Theorem  If x and y are sets, then ∪[x,y]=[x|y], ∩[x,y]=[x], ∪∩[x,y]=x,
   ∩∩[x,y]=x, ∪∪[x,y]=x∪y, ∩∪[x,y]=x∩y. If either x or y is not a set,
   then ∪∩[x,y]=Φ, ∩∩[x,y]=Φ, ∪∪[x,y]=Φ, ∩∪[x,y]=Φ. *)

Lemma lem_set_ele_orde : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x] /\ Ensemble [x | y].
Proof.
  intros; apply ord_set in H; auto.
  unfold Ordered in H; unfold Unordered in H.
  apply Axiom_Union' in H; destruct H.
  apply sing_set_inv in H; auto.
  apply sing_set_inv in H0; auto.
Qed.

Theorem set_ele_orde : forall (x y: Class),
  Ensemble x /\ Ensemble y -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\
  (∪(∩[x,y]) = x) /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  intros; elim H; intros.
  repeat unfold Ordered; apply lem_set_ele_orde in H.
  apply unord_ele in H; auto; elim H; intros; repeat split.
  - rewrite H3; apply Axiom_Extent; split; intros; try (apply bel_union; tauto).
    apply bel_union in H4; destruct H4; auto; apply bel_union; tauto.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply bel_inter in H4; apply H4.
    + apply bel_inter; split; auto; apply bel_union; tauto.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4, H5, H5. 
      apply bel_inter in H6; destruct H6; apply Axiom_Scheme in H6.
      destruct H6; rewrite <- H8; auto.
      apply bel_universe_set; auto.
    + apply Axiom_Scheme; split; Ens; exists x. 
      split; auto; apply bel_inter; split.
      * apply Axiom_Scheme; split; auto.
      * apply bel_union; left; apply Axiom_Scheme.
        split; try apply H0; trivial.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4.
      apply H5; apply bel_inter; split.
      * apply Axiom_Scheme; split; auto.
      * apply bel_union; left; apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme; split; Ens.
      intros; apply bel_inter in H5. destruct H5. 
      apply Axiom_Scheme in H5. destruct H5. rewrite H7; auto. 
      apply bel_universe_set; auto.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply bel_union; apply Axiom_Scheme in H4; destruct H4, H5, H5. 
      apply bel_union in H6; destruct H6.
      * apply Axiom_Scheme in H6; destruct H6; left; rewrite <- H7; auto. 
        apply bel_universe_set; auto.
      * apply bel_union in H6; destruct H6. 
        -- apply Axiom_Scheme in H6; destruct H6.
           left; rewrite <- H7; auto; apply bel_universe_set; auto.
        -- apply Axiom_Scheme in H6; destruct H6.
           right; rewrite <- H7; auto; apply bel_universe_set; auto.
    + apply Axiom_Scheme; apply bel_union in H4; split.
      * unfold Ensemble; destruct H4; Ens.
      * destruct H4.
        -- exists x; split; auto; apply bel_union; left.
           apply Axiom_Scheme; split; auto.
        -- exists y; split; auto; apply bel_union; right.
           apply bel_union; right; apply Axiom_Scheme; split; auto.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Lemma_x in H4; elim H4; intros.
      apply Axiom_Scheme in H5; apply Axiom_Scheme in H6.
      destruct H4; apply bel_inter; split; auto.
      * apply H5; apply bel_union; left.
        apply Axiom_Scheme; split; auto.
      * apply H6; apply bel_union; right.
        apply bel_union; right.
        apply Axiom_Scheme; split; auto.
    + apply bel_inter in H4; destruct H4. 
      apply Axiom_Scheme; split; Ens.
      intros; apply bel_union in H6; destruct H6.
      * apply Axiom_Scheme in H6; destruct H6; rewrite H7; auto.
        apply bel_universe_set; auto.
      * apply Axiom_Scheme in H6; destruct H6, H7.
        -- apply Axiom_Scheme in H7; destruct H7. 
           rewrite H8; auto; apply bel_universe_set; auto.
        -- apply Axiom_Scheme in H7; destruct H7.
           rewrite H8; auto; apply bel_universe_set; auto.
Qed.

Lemma lem_set_ele_orde' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> ~Ensemble [x] \/ ~Ensemble [x | y].
Proof.
  intros; elim H; intros. 
  - left; apply sing_eq_universe_iff_not_set in H0; auto.
    rewrite H0; apply universe_notset; auto.
  - right; apply unord_notset in H; auto.
    rewrite H; apply universe_notset; auto.
Qed.

Theorem set_ele_orde' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ)
  /\ (∪(∪[x,y]) = μ) /\ (∩(∪[x,y]) = Φ).
Proof.
  intros; apply lem_set_ele_orde' in H; auto.
  apply unord_ele_not in H; destruct H.
  repeat unfold Ordered; repeat split.
  - rewrite H; apply zero_eleU_zero; auto.
  - rewrite H; apply zero_eleI_universe; auto.
  - rewrite H0; rewrite <- universe_eleU; auto.
  - rewrite H0; rewrite <- universe_eleI; auto.
Qed.

Hint Resolve set_ele_orde set_ele_orde' : set.


(* 51 Definition  1st coord z = ∩∩z. *)

Definition First z := ∩∩z.

Hint Unfold First : set.


(* 52 Definition  2nd coord z = (∩∪z)∪(∪∪z)~(∪∩z). *)

Definition Second z := (∩∪z)∪(∪∪z)~(∪∩z).

Hint Unfold Second : set.


(* 53 Theorem  2nd coord μ = μ. *)

Lemma universe_diff_zero : μ ~ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply bel_inter in H; destruct H; auto.
  - apply bel_inter; split; auto.
    apply Axiom_Scheme; split.
    * apply bel_universe_set in H; auto.
    * apply not_bel_zero; auto.
Qed.

Theorem snd_U : Second μ = μ.
Proof.
  intros; unfold Second.
  repeat rewrite <-universe_eleU; auto.
  repeat rewrite <-universe_eleI ; auto.
  rewrite zero_eleU_zero; auto.
  rewrite universe_diff_zero; auto.
  apply universe_union; auto.
Qed.

Hint Rewrite snd_U : set.


(* 54 Theorem  If x and y are sets, 1st coord [x,y] = x and 2nd coord [x,y] = y.
   If either of x and y is not a set, then 1st coord [x,y] = μ and
   2nd coord [x,y] = μ. *)

Lemma union_diff : forall (x y: Class),
  (x ∪ y) ~ x = y ~ x.
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - apply bel_inter in H; apply bel_inter.
    destruct H; apply bel_union in H; split; auto.
    destruct H; auto; apply Axiom_Scheme in H0.
    destruct H0; elim H1; auto.
  - apply bel_inter in H; apply bel_inter.
    destruct H; split; auto.
    apply bel_union; tauto.
Qed.

Theorem ordere_fst_snd : forall (x y: Class),
  Ensemble x /\ Ensemble y -> First [x,y] = x /\ Second [x,y] = y.
Proof.
  intros; apply set_ele_orde in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1, H2, H3; unfold Second.
    rewrite H4; rewrite H3; rewrite H1.
    rewrite union_diff; auto; unfold Difference.
    rewrite inter_com; auto; rewrite <- union_dist; auto.
    rewrite Property_μ; auto; rewrite universe_inter; auto.
Qed.


Theorem not_ordere_fst_snd : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> First [x,y] = μ /\ Second [x,y] = μ.
Proof.
  intros; apply set_ele_orde' in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1; unfold Second.
    rewrite H2; rewrite H1; rewrite H.
    rewrite universe_diff_zero; auto.
    apply universe_union; auto.
Qed.

Hint Resolve ordere_fst_snd not_ordere_fst_snd : set.


(* 55 Theorem  If x and y are sets and [x,y] = [u,v], then x=u and y=v. *)

Theorem ord_eq : forall (x y u v: Class),
  Ensemble x /\ Ensemble y -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  intros; split; intros.
  - double H; apply ord_set in H; apply ordere_fst_snd in H1; destruct H1.
    rewrite H0 in H, H1, H2; apply ord_set in H; apply ordere_fst_snd in H.
    destruct H; rewrite H1 in H; rewrite H2 in H3; split; auto.
  - destruct H0; rewrite H0, H1; auto.
Qed.

Hint Resolve ord_eq : set.


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

Theorem compo_ass : forall (r s t: Class),
  (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H a b. apply Axiom_SchemeP in H0; destruct H0, H1 as [y H1], H1.
    apply Axiom_SchemeP in H2; destruct H2, H3, H3.
    apply Axiom_SchemeP; split; auto.
    exists x; split; try tauto; apply Axiom_SchemeP; split; Ens.
    AssE [a,y]; AssE [y,x]; apply ord_set in H5; apply ord_set in H6.
    destruct H5, H6; apply ord_set; auto.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0, H1 as [y H1], H1.
    apply Axiom_SchemeP in H1; destruct H1, H3, H3.
    apply Axiom_SchemeP; split; auto.
    exists x; split; auto; apply Axiom_SchemeP; split; Ens.
    AssE [a,x]; AssE [y,b]; apply ord_set in H5; apply ord_set in H6.
    destruct H5, H6; apply ord_set; Ens.
Qed.

Hint Rewrite compo_ass : set.


(* 59 Theorem  r∘(s∪t) = r∘s ∪ r∘t and r∘(s∩t) ⊂ r∘s ∩ r∘t. *)

Theorem rel_compo : forall (r s t: Class),
  Relation r /\ Relation s -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t) /\ 
  r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  intros; split.
  - apply Axiom_Extent; split; intros.
    + PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
      apply bel_union.
      destruct H2 as [y H2]; destruct H2.
      apply bel_union in H2; destruct H2.
      * left; apply Axiom_SchemeP; split; auto.
        exists y; split; auto.
      * right; apply Axiom_SchemeP; split; auto.
        exists y; split; auto.
    + apply bel_union in H0; destruct H0; PP H0 a b; apply Axiom_SchemeP.
      * apply Axiom_SchemeP in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply bel_union; try tauto.
      * apply Axiom_SchemeP in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply bel_union; try tauto.
  - unfold Subclass; intros; PP H0 a b.
    apply Axiom_SchemeP in H1; destruct H1.
    destruct H2 as [y H2]; destruct H2.
    apply bel_inter in H2; apply bel_inter; split.
    + apply Axiom_SchemeP; split; auto.
      exists y; split; try apply H2; auto.
    + apply Axiom_SchemeP; split; auto.
      exists y; split; try apply H2; auto.
Qed.

Hint Resolve rel_compo : set.


(* 60 Definition  r⁻¹ = { [x,y] : [y,x] ∈ r }. *)

Definition Inverse r : Class := \{\ λ x y, [y,x]∈r \}\.

Notation "r ⁻¹" := (Inverse r)(at level 5).

Hint Unfold Inverse : set.


(* 61 Theorem  If r is a relation, then (r⁻¹)⁻¹ = r. *)

Lemma orde_set_iff : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble [y,x].
Proof.
  intros; split; intros.
  - apply ord_set in H; auto.
    destruct H; apply ord_set; auto.
  - apply ord_set in H; auto.
    destruct H; apply ord_set; auto.
Qed.

Theorem rel_inv_fix : forall (r: Class),
  Relation r -> (r ⁻¹)⁻¹ = r.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
    apply Axiom_SchemeP in H2; apply H2.
  - unfold Relation in H; double H0; apply H in H1.
    destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply Axiom_SchemeP; split; Ens; apply Axiom_SchemeP; split; auto.
    apply orde_set_iff; auto; Ens.
Qed.

Hint Rewrite rel_inv_fix : set.


(* 62 Theorem  (r∘s)⁻¹ = (s⁻¹) ∘ (r⁻¹). *)

Theorem comp_inv_dist : forall (r s: Class),
  (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0 as [H0 H1].
    apply Axiom_SchemeP; split; auto.
    apply Axiom_SchemeP in H1; destruct H1, H2, H2.
    exists x; split.
    + apply Axiom_SchemeP; split; auto. 
      apply orde_set_iff; Ens; exists r; auto.
    + apply Axiom_SchemeP; split; auto.
      apply orde_set_iff; Ens.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0, H1, H1.
    apply Axiom_SchemeP; split; auto.
    apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    apply Axiom_SchemeP; split.
    + apply orde_set_iff; auto.
    + exists x; split; try apply H0; try apply H2.
      destruct H1; auto.
Qed.

Hint Rewrite comp_inv_dist : set.


End OrderedP.

Export OrderedP.

