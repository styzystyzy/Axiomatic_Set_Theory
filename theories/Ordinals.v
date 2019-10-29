Require Export theories.Well_Ordering.


(* ORDINALS *)

Module Ord.

(* VII Axiom of regularity : If x ≠ Φ there is a member y of x such x∩y = Φ. *)

Axiom Axiom_Regularity : forall x, x ≠ Φ -> exists y, y ∈ x /\ x ∩ y = Φ.

Hint Resolve Axiom_Regularity : set.


(* 101 notin_fix  x ∉ x. *)

Theorem notin_fix : forall x, x ∉ x.
Proof.
  intros; intro.
  assert ([x] ≠ Φ).
  { apply not_zero_exist_bel; exists x; apply Axiom_Scheme; split; Ens. }
  apply Axiom_Regularity in H0; destruct H0, H0.
  assert (x0 = x).
  { apply Axiom_Scheme in H0; destruct H0; apply H2; apply bel_universe_set; Ens. }
  subst x0; assert (x ∈ ([x] ∩ x)). { apply Axiom_Scheme; repeat split; Ens. }
  rewrite H1 in H2; generalize (not_bel_zero x); intro; contradiction.
Qed.

Hint Resolve notin_fix : set.


(* 102 Theorem  It is false that x∈y and y∈x. *)

Theorem not_bel_and : forall x y, ~ (x ∈ y /\ y ∈ x).
Proof.
  intros; intro; destruct H.
  assert (\{ λ z, z = x \/ z =y \} ≠ Φ).
  { apply not_zero_exist_bel; exists x; apply Axiom_Scheme; split; Ens. }
  apply Axiom_Regularity in H1; destruct H1, H1; apply Axiom_Scheme in H1.
  destruct H1, H3; subst x0.
  + assert (y ∈ (\{ λ z, z = x \/ z = y \} ∩ x)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H3; generalize (not_bel_zero y); intro; contradiction.
  + assert (x ∈ (\{ λ z, z = x \/ z = y \} ∩ y)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H3; generalize (not_bel_zero x); intro; contradiction.
Qed.

Hint Resolve not_bel_and : set.


(* 103 Definition  E = { [x,y] : x∈y}. *)

Definition E : Class := \{\ λ x y, x ∈ y \}\.

Hint Unfold E : set.


(* 104 Theorem  E is not a set. *)

Lemma bel_tran_false : forall a b c, a ∈ b -> b ∈ c -> c ∈ a -> False.
Proof.
  intros.
  assert (\{ λ x, x = a \/ x =b \/ x = c \} ≠ Φ).
  { apply not_zero_exist_bel; exists a; apply Axiom_Scheme; split; Ens. }
  apply Axiom_Regularity in H2; destruct H2, H2; apply Axiom_Scheme in H2; destruct H2.
  destruct H4 as [H4 | [H4 | H4]]; subst x.
  + assert (c ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ a)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H3 in H4; generalize (not_bel_zero c); intro; contradiction.
  + assert (a ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ b)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H3 in H4; generalize (not_bel_zero a); intro; contradiction.
  + assert (b ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ c)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H3 in H4; generalize (not_bel_zero b); intro; contradiction.
Qed.

Theorem not_set_E : ~ Ensemble E.
Proof.
  intro; generalize (sing_set _ H); intro.
  assert (E ∈ [E]). { apply Axiom_Scheme; split; auto. }
  assert ([E, [E]] ∈ E).
  { apply Axiom_SchemeP; split; auto; apply ord_set; tauto. }
  assert ([E] ∈ [E, [E]]).
  { apply Axiom_Scheme; split; Ens; left; apply Axiom_Scheme; split; auto. }
  eapply bel_tran_false; eauto.
Qed.

Hint Resolve not_set_E : set.


(* 105 Definition  x is full iff each member of x is a subset of x. *)

Definition full x : Prop := forall m, m∈x -> m⊂x.

Corollary Property_Full : forall x, 
  full x <-> (forall u v : Class, v ∈ x /\ u ∈ v -> u ∈ x).
Proof.
  intros; split; intros.
  - unfold full in H; destruct H0; apply H in H0; auto.
  - unfold full; intros; unfold Subclass; intros; apply H with m; tauto.
Qed.

Hint Unfold full : set.
Hint Resolve Property_Full : set.


(* 106 Definition  x is an ordinal iff E connects x and x is full. *)

Definition Ordinal x : Prop := Connect E x /\ full x.

Hint Unfold Ordinal : set.


(* 107 Theorem  If x is an ordinal E well-orders x. *)

Theorem ord_well_order : forall x, 
  Ordinal x -> WellOrdered E x.
Proof.
  intros.
  unfold Ordinal in H; destruct H; unfold WellOrdered.
  intros; split; auto; intros; destruct H1.
  apply Axiom_Regularity in H2; destruct H2, H2.
  exists x0; unfold FirstMember; intros.
  split; auto; intros; intro.
  unfold Rrelation in H5; apply Axiom_SchemeP in H5; destruct H5.
  assert (y0 ∈ (y ∩ x0)). { apply Axiom_Scheme; split; Ens. }
  rewrite H3 in H7; generalize (not_bel_zero y0); intro; contradiction.
Qed.

Hint Resolve ord_well_order : set.


(* 108 Theorem  If x is an ordinal, y⊂x, y≠x, and y is full, then y∈x. *)

Theorem ord_sub_full_bel : forall x y, 
  Ordinal x -> y ⊂ x -> y≠x -> full y -> y ∈ x.
Proof.
  intros.
  assert (Section y E x).
  { apply ord_well_order in H; unfold Section; intros.
    split; auto; split; auto; intros; destruct H3, H4.
    unfold Rrelation in H5; apply Axiom_SchemeP in H5; destruct H5.
    unfold full in H2; apply H2 in H4; auto. }
  generalize (Lemma_xy _ _ H3 H1); intro.
  apply sec_noteq_exist_set in H4; destruct H4, H4.
  assert (x0 = \{ λ u : Class,u ∈ x /\ Rrelation u E x0 \}).
  { apply Axiom_Extent; split; intros; AssE z.
    - apply Axiom_Scheme; split; auto.
      unfold Ordinal in H; destruct H.
      double H4; unfold full in H8; apply H8 in H4.
      split; auto; apply Axiom_SchemeP; split; auto.
      apply ord_set; split; Ens.
    - apply Axiom_Scheme in H6; destruct H6, H8.
      unfold Rrelation in H9; apply Axiom_SchemeP in H9; tauto. }
  rewrite <- H6 in H5; subst x0; auto.
Qed.

Hint Resolve ord_sub_full_bel : set.


(* 109 Theorem  If x is an ordinal an y is an ordinal, then x⊂y or y⊂x. *)

Lemma ord_full_int : forall x y,
  Ordinal x /\ Ordinal y -> full (x ∩ y).
Proof.
  intros; destruct H; unfold Ordinal in H, H0; destruct H, H0.
  unfold full in *; intros; apply Axiom_Scheme in H3; destruct H3, H4.
  apply H1 in H4; apply H2 in H5.
  unfold Subclass; intros; apply Axiom_Scheme; repeat split; Ens.
Qed.

Lemma ord_int_or : forall x y,
  Ordinal x /\ Ordinal y -> ((x ∩ y) = x) \/ ((x ∩ y) ∈ x).
Proof.
  intros.
  generalize (classic ((x ∩ y) = x)); intro; destruct H0; try tauto.
  assert ((x ∩ y) ⊂ x).
  { unfold Subclass; intros; apply bel_inter in H1; tauto. }
  elim H; intros; apply ord_full_int in H.
  eapply ord_sub_full_bel in H2; eauto.
Qed.

Theorem ord_sub_or : forall x y,
  Ordinal x /\ Ordinal y -> x ⊂ y \/ y ⊂ x.
Proof.
  intros; elim H; intros; generalize (Lemma_xy _ _ H1 H0); intro.
  apply ord_int_or in H; apply ord_int_or in H2; destruct H.
  - apply inter_sub in H; tauto.
  - destruct H2.
    + apply inter_sub in H2; tauto.
    + assert ((x ∩ y) ∈ (x ∩ y)).
      { rewrite inter_com in H2; apply Axiom_Scheme; repeat split; Ens. }
      apply notin_fix in H3; elim H3.
Qed.

Hint Resolve ord_sub_or : set.


(* 110 Theorem  If x is an ordinal an y is an ordinal, then x∈y or y∈x or
   x = y. *)

Theorem ord_bel_eq : forall x y,
  Ordinal x /\ Ordinal y -> x ∈ y \/ y ∈ x \/ x = y.
Proof.
  intros; generalize (classic (x = y)); intro; destruct H0; try tauto.
  elim H; intros; apply ord_sub_or in H; destruct H.
  - left; unfold Ordinal in H1; destruct H1; eapply ord_sub_full_bel; eauto.
  - right; left; unfold Ordinal in H2; destruct H2.
    eapply ord_sub_full_bel; eauto; intro; auto.
Qed.

Hint Resolve ord_bel_eq : set.


(* 111 Theorem  If x is an ordinal and y∈x, then y is an ordinal. *)

Theorem ord_bel_ord : forall x y, Ordinal x /\ y ∈ x -> Ordinal y.
Proof.
  intros; destruct H; double H; unfold Ordinal in H; destruct H.
  assert (Connect E y).
  { unfold Connect; intros; unfold Ordinal in H1; apply H1 in H0.
    unfold Connect in H; destruct H3; apply H; auto. }
  unfold Ordinal; split; auto.
  unfold full; intros; unfold Subclass; intros.
  apply ord_well_order in H1; unfold Ordinal in H1.
  assert (y ⊂ x); auto; assert (m ∈ x); auto.
  assert (m ⊂ x); auto; assert (z ∈ x); auto.
  apply well_tran_asy in H1; destruct H1.
  unfold Transitive in H1; specialize H1 with z m y.
  assert (Rrelation z E y).
  { apply H1; repeat split; Ens.
    - unfold Rrelation; apply Axiom_SchemeP; split; auto.
      apply ord_set; split; Ens.
    - unfold Rrelation; apply Axiom_SchemeP; split; auto.
      apply ord_set; split; Ens. }
  unfold Rrelation in H11; apply Axiom_SchemeP in H11; tauto.
Qed.

Hint Resolve ord_bel_ord : set.


(* 112 Definition  R = { x : x is an ordinal }. *)

Definition R : Class := \{ λ x, Ordinal x \}.

Hint Unfold R : set.


(* 113 Theorem  R is an ordinal and R is not a set. *)

Lemma Lemma113 :forall u v,
  Ensemble u -> Ensemble v -> Ordinal u /\ Ordinal v ->
  (Rrelation u E v \/ Rrelation v E u \/ u = v) .
Proof.
  intros; apply ord_bel_eq in H1; repeat split.
  destruct H1 as [H1 | [H1 | H1]].
  - left; unfold Rrelation; apply Axiom_SchemeP; split; Ens.
    apply ord_set; auto.
  - right; left; apply Axiom_SchemeP; split; Ens.
    apply ord_set; auto.
  - right; right; auto.
Qed.

Theorem ord_not_set_R : Ordinal R /\ ~ Ensemble R.
Proof.
  intros.
  assert (Ordinal R).
  { unfold Ordinal; intros; split.
    - unfold Connect; intros; destruct H.
      apply Axiom_Scheme in H; destruct H; apply Axiom_Scheme in H0; destruct H0.
      generalize (Lemma_xy _ _ H1 H2); intro; apply Lemma113; auto.
    - unfold full; intros; apply Axiom_Scheme in H; destruct H.
      unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
      eapply ord_bel_ord; eauto. }
  split; auto; intro.
  assert (R ∈ R). { apply Axiom_Scheme; split; auto. }
  apply notin_fix in H1; auto.
Qed.

Hint Resolve ord_not_set_R : set.


(* 114 Theorem  Each E-section of R is an ordinal. *)

Theorem sec_R_ord : forall x, Section x E R -> Ordinal x.
Proof.
  intros.
  generalize (classic (x = R)); intro; destruct H0.
  - rewrite H0; apply ord_not_set_R.
  - generalize (Lemma_xy _ _ H H0); intro.
    apply sec_noteq_exist_set in H1; destruct H1, H1.
    assert (x0 = \{ λ u, u ∈ R /\ Rrelation u E x0 \}).
    { apply Axiom_Extent; split; intros.
      - apply Axiom_Scheme; repeat split; Ens.
        + apply Axiom_Scheme in H1; destruct H1.
          apply Axiom_Scheme; split; Ens; eapply ord_bel_ord; eauto.
        + unfold Rrelation; apply Axiom_SchemeP; split; auto.
          apply ord_set; Ens.
      - apply Axiom_Scheme in H3; destruct H3, H4.
        unfold Rrelation in H5; apply Axiom_SchemeP in H5; tauto. }
    subst x; rewrite H3 in H1; apply Axiom_Scheme in H1; tauto.
Qed.

Corollary ord_sec_R : forall x, Ordinal x -> Section x E R.
Proof.
  intros; unfold Section; split.
  - unfold Subclass; intros; apply Axiom_Scheme; split; try Ens.
    eapply ord_bel_ord; eauto.
  - split; intros; try apply ord_well_order; try apply ord_not_set_R.
    destruct H0, H1; unfold Ordinal in H2; apply Axiom_SchemeP in H2.
    destruct H2; unfold Ordinal in H; destruct H; apply H4 in H1; auto.
Qed.


Hint Resolve sec_R_ord : set.


(* 115 Definition  x is an ordinal number iff x ∈ R. *)

Definition Ordinal_Number x : Prop := x ∈ R.

Hint Unfold Ordinal_Number : set.


(* 116 Definition  x ≺ y if and only if x ∈ y. *)

Definition Less x y : Prop := x ∈ y.

Notation "x ≺ y" := (Less x y)(at level 67, left associativity).

Hint Unfold Less : set.


(* 117 Definition  x ≼ y if and only if x ∈ y or x = y. *)

Definition LessEqual x y := x ∈ y \/ x=y.

Notation "x ≼ y" := (LessEqual x y)(at level 67, left associativity).


(* 118 Theorem  If x and y are ordinals, then x ≼ y if and only if x ⊂ y. *)

Theorem ord_sub_iff_le : forall x y,
  Ordinal x /\ Ordinal y -> (x ⊂ y <-> x ≼ y).
Proof.
  intros; destruct H; split; intros.
  - unfold LessEqual.
    generalize (classic (x = y)); intro; destruct H2; try tauto.
    unfold Ordinal in H; destruct H.
    left; apply ord_sub_full_bel; auto.
  - unfold LessEqual in H1; destruct H1.
    + unfold Ordinal in H0; destruct H0; auto.
    + rewrite H1; auto; unfold Subclass; intros; auto.
Qed.

Hint Resolve ord_sub_iff_le : set.


(* 119 Theorem  If x is an ordinal, then x = { y : y ∈ R /\ y ≺ x }. *)

Theorem ord_set_eq : forall x,
  Ordinal x -> x = \{ λ y, y ∈ R /\ y ≺ x \}.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; repeat split; Ens.
    apply Axiom_Scheme; split; Ens; eapply ord_bel_ord; eauto.
  - apply Axiom_Scheme in H0; destruct H0, H1; auto.
Qed.

Hint Resolve ord_set_eq : set.


(* 120 Theorem  If x ⊂ R, then ∪x is an ordinal. *)

Theorem sub_ord_eleU : forall x, x ⊂ R -> Ordinal (∪ x).
Proof.
  intros; red; split.
  - unfold Connect; intros; destruct H0; apply Axiom_Scheme in H0.
    apply Axiom_Scheme in H1; destruct H0, H2, H2, H1, H4, H4.
    apply H in H3; apply H in H5; apply Axiom_Scheme in H3.
    destruct H3; apply Axiom_Scheme in H5; destruct H5.
    assert (Ordinal u). { eapply ord_bel_ord; eauto. }
    assert (Ordinal v). { eapply ord_bel_ord; eauto. }
    generalize (Lemma_xy _ _ H8 H9); intro; apply Lemma113; auto.
  - apply Property_Full; intros; destruct H0.
    apply Axiom_Scheme in H0; destruct H0, H2, H2.
    apply Axiom_Scheme; split; Ens; exists x0; split; auto.
    apply H in H3; apply Axiom_Scheme in H3; destruct H3 as [_ H3].
    unfold Ordinal in H3; destruct H3; apply H4 in H2; auto.
Qed.

Hint Resolve sub_ord_eleU : set.


(* 121 Theorem  If x ⊂ R and x ≠ Φ, then ∩x ∈ x. *)

Lemma sub_noteq_firstmemb : forall x, x ⊂ R /\ x ≠ Φ -> FirstMember (∩ x) E x.
Proof.
  intros; destruct H.
  generalize (ord_not_set_R); intro; destruct H1.
  apply ord_well_order in H1; unfold WellOrdered in H1; destruct H1.
  generalize (Lemma_xy _ _ H H0); intro; apply H3 in H4; destruct H4.
  double H4; unfold FirstMember in H4; destruct H4.
  assert ((∩ x) = x0).
  { apply Axiom_Extent; split; intros.
    - apply Axiom_Scheme in H7; destruct H7; apply H8; auto.
    - apply Axiom_Scheme; split; Ens; intros.
      assert (~ Rrelation y E x0); auto.
      assert (Ordinal x0). { apply H in H4; apply Axiom_Scheme in H4; tauto. }
      assert (Ordinal y). { apply H in H8; apply Axiom_Scheme in H8; tauto. }
      generalize (Lemma_xy _ _ H10 H11); intro; apply ord_bel_eq in H12.
      destruct H12 as [H12 | [H12 | H12]].
      + apply H in H8; apply Axiom_Scheme in H8; destruct H8 as [_ H8].
        unfold Ordinal in H8; destruct H8; generalize (Property_Full y); intro.
        destruct H14; eapply H14; eauto.
      + elim H9; unfold Rrelation; apply Axiom_SchemeP; split; auto.
        apply ord_set; Ens.
      + subst x0; auto. }
  rewrite H7 ; auto.
Qed.

Theorem sub_noteq_eleI : forall x, x ⊂ R /\ x ≠ Φ -> (∩ x) ∈ x.
Proof.
  intros; apply sub_noteq_firstmemb in H.
  unfold FirstMember in H; tauto.
Qed.

Hint Resolve sub_noteq_eleI : set.


(* 122 Definition  x + 1 = x ∪ {x}. *)

Definition PlusOne x := x ∪ [x].

Hint Unfold PlusOne: set.


(* 123 Theorem  If x∈R, then x+1 is the E-first member of {y : y∈R and x≺y}. *)

Lemma ordnum_succ_ordnum : forall x, x ∈ R -> (PlusOne x) ∈ R.
Proof.
  intros; apply Axiom_Scheme; split.
  - apply Axiom_Union; split; Ens; apply sing_set; Ens.
  - unfold Connect; split.
    + unfold Connect; intros; destruct H0.
      apply Axiom_Scheme in H0; apply Axiom_Scheme in H1; destruct H0, H1, H2, H3.
      * apply Axiom_Scheme in H; destruct H as [_ H].
        assert (Ordinal u). { eapply ord_bel_ord; eauto. }
        assert (Ordinal v). { eapply ord_bel_ord; eauto. }
        generalize (Lemma_xy _ _ H4 H5); intro; apply Lemma113; auto.
      * apply Axiom_Scheme in H3; destruct H3.
        AssE x; apply bel_universe_set in H5; apply H4 in H5; subst v.
        left; unfold Rrelation; apply Axiom_SchemeP; split; auto.
        apply ord_set; tauto.
      * apply Axiom_Scheme in H2; destruct H2.
        AssE x; apply bel_universe_set in H5; apply H4 in H5; subst u.
        right; left; unfold Subclass; apply Axiom_SchemeP; split; auto.
        apply ord_set; tauto.
      * AssE x; apply bel_universe_set in H4; double H4.
        apply Axiom_Scheme in H2; destruct H2; apply H6 in H4.
        apply Axiom_Scheme in H3; destruct H3; apply H7 in H5.
        subst u; subst v; tauto.
    + unfold full; intros; unfold Subclass; intros.
      apply Axiom_Scheme in H; apply Axiom_Scheme in H0; destruct H, H0.
      apply Axiom_Scheme; split; Ens; destruct H3.
      * unfold Ordinal in H2; destruct H2.
        unfold full in H4; left; eapply H4; eauto.
      * apply Axiom_Scheme in H3; destruct H3.
        apply bel_universe_set in H; apply H4 in H; subst m; tauto.
Qed.

Theorem ordnum_firstmemb : forall x,
  x ∈ R -> FirstMember (PlusOne x) E (\{ λ y, (y ∈ R /\ Less x y) \}).
Proof.
  intros; unfold FirstMember; split; intros.
  - apply Axiom_Scheme; repeat split.
    + unfold Ensemble; exists R; apply ordnum_succ_ordnum; auto.
    + apply ordnum_succ_ordnum; auto.
    + unfold Less; intros; apply Axiom_Scheme; split; Ens.
      right; apply Axiom_Scheme; split; Ens.
  - intro; apply Axiom_Scheme in H0; destruct H0, H2.
    unfold Rrelation in H1; apply Axiom_SchemeP in H1; destruct H1.
    apply Axiom_Scheme in H4; destruct H4; unfold Less in H3; destruct H5.
    + eapply not_bel_and; eauto.
    + AssE x; apply bel_universe_set in H6; apply Axiom_Scheme in H5; destruct H5.
      apply H7 in H6; subst y; eapply notin_fix; eauto.
Qed.

Hint Resolve ordnum_firstmemb : set.


(* 124 Theorem  If x ∈ R, then ∪(x+1) = x. *)

Theorem ordnum_eleU_succ_eq : forall x, 
  x ∈ R -> ∪ PlusOne x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0, H1, H1.
    apply Axiom_Scheme in H2; destruct H2, H3.
    + apply Axiom_Scheme in H; destruct H, H4.
      generalize (Property_Full x); intro; destruct H6.
      apply H6 with (u:=z) (v:=x0) in H5; tauto.
    + apply Axiom_Scheme in H3; destruct H3.
      rewrite <- H4; auto; try (apply bel_universe_set; Ens).
  - apply Axiom_Scheme; split; Ens; exists x; split; auto.
    apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; Ens.
Qed.

Hint Resolve ordnum_eleU_succ_eq : set.


(* 125 Definition  f|x = f ∩ (x × μ). *)

Definition Restriction f x : Class := f ∩ (x × μ).

Notation "f | ( x )" := (Restriction f x)(at level 30).

Hint Unfold Restriction: set.


(* 126 Theorem  If f is a function, f|x is a function whose domain is
   x ∩ (domain f) and (f|x)[y] = f[y] for each y in domain f|x. *)

Theorem fun_res_fun : forall f x,
  Function f -> Function (f|(x)) /\ dom(f|(x)) = x ∩ dom( f) /\
  (forall y, y ∈ dom(f|(x)) -> (f|(x)) [y] = f [y]).
Proof.
  intros; repeat split; intros.
  - unfold Relation; intros; apply Axiom_Scheme in H0; destruct H0, H1.
    PP H2 a b; eauto.
  - destruct H0; apply Axiom_Scheme in H0; destruct H0 as [_ [H0 _]].
    apply Axiom_Scheme in H1; destruct H1 as [_ [H1 _]].
    unfold Function in H; eapply H; eauto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H0; destruct H0, H1.
      apply Axiom_Scheme in H1; destruct H1, H2.
      apply Property_dom in H2; apply Axiom_SchemeP in H3.
      apply Axiom_Scheme; split; tauto.
    + apply Axiom_Scheme in H0; destruct H0, H1.
      apply Axiom_Scheme; split; auto.
      apply Property_Value in H2; auto.
      exists f[z]; apply Axiom_Scheme; repeat split; Ens.
      apply Axiom_SchemeP; repeat split; Ens; apply bel_universe_set.
      apply Property_ran in H2; Ens.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1.
      apply Axiom_Scheme in H0; destruct H0, H3.
      apply Axiom_Scheme in H3; destruct H3, H4.
      apply Property_dom in H4; apply H2.
      assert (Ensemble f[y]). { apply bel_universe_set; apply dom_value; auto. }
      apply Axiom_Scheme; split; Ens; apply Axiom_Scheme; repeat split.
      * apply ord_set; auto.
      * apply Property_Value in H4; auto.
      * apply Axiom_SchemeP in H5; apply bel_universe_set in H6.
        apply Axiom_SchemeP; repeat split; try tauto; try apply ord_set; Ens.
    + apply Axiom_Scheme in H1; destruct H1.
      apply Axiom_Scheme; split; auto; intros.
      apply Axiom_Scheme in H3; destruct H3; apply Axiom_Scheme in H4.
      apply H2; apply Axiom_Scheme; split; tauto.
Qed.

Hint Resolve fun_res_fun : set.


(* 127 Theorem  Let f be a function such that domain f is an ordinal and
   f[u] = g[f|u] for u in domain f. If h is also a function such that domain h
   is an ordinal and h[u] = g[h|u] for u in domain h, then h ⊂ f or f ⊂ h. *)

Theorem lem_fun_ord_res_sub : forall f h,
  dom( f) ⊂ dom( h) -> Function f -> Function h ->
  \{ λ a,a ∈ (dom( f) ∩ dom( h)) /\ f [a] ≠ h [a] \} = Φ -> f ⊂ h.
Proof.
  intros.
  unfold Subclass; intros; rewrite fun_set_eq in H3; auto; PP H3 a b.
  double H4; rewrite <- fun_set_eq in H4; auto; apply Property_dom in H4.
  apply Axiom_SchemeP in H5; destruct H5.
  rewrite fun_set_eq; auto; apply Axiom_SchemeP; split; auto; rewrite H6.
  generalize (classic (f[a] = h[a])); intro; destruct H7; auto.
  assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
  { apply inter_sub in H; rewrite H; apply Axiom_Scheme; split; Ens. }
  rewrite H2 in H8; generalize (not_bel_zero a); contradiction.
Qed.

Theorem fun_ord_res_sub : forall f h g,
  Function f -> Ordinal dom(f) ->
  (forall u0, u0 ∈ dom(f) -> f[u0] = g[f|(u0)]) ->
  Function h -> Ordinal dom(h) ->
  (forall u1, u1 ∈ dom(h) -> h[u1] = g [h|(u1)]) -> h ⊂ f \/ f ⊂ h.
Proof.
  intros.
  generalize (Lemma_xy _ _ H0 H3); intro; apply ord_sub_or in H5.
  generalize (classic (\{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \} = Φ));
  intro; destruct H6.
  - destruct H5.
    + right; apply lem_fun_ord_res_sub; auto.
    + left; rewrite lem_order_pre_sec_sub'' in H6; apply lem_fun_ord_res_sub; auto.
  - assert (exists u, FirstMember u E \{λ a, a∈(dom(f)∩dom(h))/\f[a]≠h[a]\}).
    { apply ord_well_order in H0; unfold WellOrdered in H0; apply H0; split; auto.
      unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
      apply Axiom_Scheme in H8; tauto. }
    destruct H7 as [u H7]; unfold FirstMember in H7; destruct H7.
    apply Axiom_Scheme in H7; destruct H7, H9.
    apply Axiom_Scheme in H9; destruct H9 as [_[H9 H11]].
    generalize (H1 _ H9); generalize (H4 _ H11); intros.
    assert ((h | (u)) = (f | (u))).
    { apply Axiom_Extent; intros; split; intros.
      - apply Axiom_Scheme in H14; destruct H14, H15.
        apply Axiom_Scheme; repeat split; auto; PP H16 a b.
        apply Axiom_SchemeP in H17; destruct H17 ,H18.
        generalize H15 as H22; intro; apply Property_dom in H22.
        rewrite fun_set_eq in H15; auto; rewrite fun_set_eq; auto.
        apply Axiom_SchemeP in H15; destruct H15.
        apply Axiom_SchemeP; split; auto.
        rewrite H20; symmetry.
        generalize (classic (f [a] = h [a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply Axiom_Scheme.
          repeat split; Ens; apply Axiom_Scheme; repeat split; Ens.
          unfold Ordinal in H0; destruct H0; apply H23 in H9; auto. }
        apply H8 in H23; elim H23; unfold Rrelation, E.
        apply Axiom_SchemeP; split; auto; apply ord_set; split; Ens.
      - apply Axiom_Scheme in H14; destruct H14, H15.
        apply Axiom_Scheme; repeat split; auto; PP H16 a b.
        apply Axiom_SchemeP in H17; destruct H17 ,H18.
        generalize H15 as H22; intro; apply Property_dom in H22.
        rewrite fun_set_eq in H15; auto; rewrite fun_set_eq; auto.
        apply Axiom_SchemeP in H15; destruct H15.
        apply Axiom_SchemeP; split; auto.
        rewrite H20; symmetry.
        generalize (classic (f[a] = h[a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply Axiom_Scheme.
          repeat split; Ens; apply Axiom_Scheme; repeat split; Ens.
          unfold Ordinal in H3; destruct H3; apply H23 in H11; auto. }
        apply H8 in H23; elim H23; unfold Rrelation, E.
        apply Axiom_SchemeP; split; auto; apply ord_set; split; Ens. }
  rewrite <- H14 in H13; rewrite <- H12 in H13; contradiction.
Qed.

Hint Resolve fun_ord_res_sub : set.


(* 128 Theorem  For each g there is a unique function f such that domain f is
   an ordinal and f[x] = g[f|x] for each ordinal number x. *)

Definition En_f' g := \{\ λ u v, u ∈ R /\ (exists h, Function h /\
  Ordinal dom(h) /\ (forall z, z ∈ dom(h) -> h[z] = g [h | (z)] ) /\
  [u,v] ∈ h ) \}\.

Lemma lem_fun_ord_dom_value_res_eq : forall u v w,
  Ordinal u -> v ∈ u -> w ∈ v -> w ∈ u.
Proof.
  intros; unfold Ordinal in H; destruct H.
  unfold full in H2; eapply H2; eauto.
Qed.

Lemma lem_fun_ord_dom_value_res_eq' : forall f x,
  Function f -> Ordinal dom(f) -> Ordinal_Number x ->
  ~ x ∈ dom(f) -> f | (x) = f .
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H3; tauto.
  - apply Axiom_Scheme; split; Ens; split; auto.
    unfold Function, Relation in H; destruct H as [H _].
    double H3; apply H in H4; destruct H4 as [a [b H4]]; rewrite H4 in *.
    clear H H4; apply Axiom_SchemeP; split; Ens; split.
    + unfold Ordinal in H1; apply Axiom_Scheme in H1; destruct H1.
      assert (Ordinal dom(f) /\ Ordinal x); auto.
      apply ord_bel_eq in H4; apply Property_dom in H3; auto.
      destruct H4 as [H4 | [H4 | H4]]; try contradiction.
      * eapply lem_fun_ord_dom_value_res_eq; eauto.
      * rewrite H4 in H3; auto.
    + apply Property_ran in H3; apply bel_universe_set; Ens.
Qed.

Theorem fun_ord_dom_value_res_eq :  forall g,
  exists f, Function f /\ Ordinal dom(f) /\
  (forall x, Ordinal_Number x -> f [x] = g [f | (x)]).
Proof.
  intros; exists (En_f' g).
  assert (Function (En_f' g)).
  { unfold Function; intros; split; intros.
    - unfold Relation; intros; PP H a b; eauto.
    - destruct H; apply Axiom_SchemeP in H; apply Axiom_SchemeP in H0.
      destruct H, H1, H2, H2, H3, H4, H0, H6, H7, H7, H8, H9.
      generalize (fun_ord_res_sub _ _ _ H2 H3 H4 H7 H8 H9); intro; destruct H11.
      + apply H11 in H10; eapply H2; eauto.
      + apply H11 in H5; eapply H7; eauto. }
  split; auto.
  - assert (Ordinal dom(En_f' g)).
    { apply sec_R_ord; unfold Section; intros; split.
      - unfold Subclass; intros; apply Axiom_Scheme in H0.
        destruct H0, H1; apply Axiom_SchemeP in H1; tauto.
      - split; intros.
        + apply ord_well_order; apply ord_not_set_R.
        + destruct H0, H1; apply Axiom_Scheme in H1; destruct H1, H3.
          apply Axiom_SchemeP in H3; destruct H3, H4, H5, H5, H6, H7.
          apply Axiom_SchemeP in H2; destruct H2.
          apply ord_set in H2; destruct H2.
          apply Axiom_Scheme; split; auto; apply Property_dom in H8.
          assert (u ∈ dom( x0)). { eapply lem_fun_ord_dom_value_res_eq; eauto. }
          exists (x0[u]); apply Axiom_SchemeP.
          split; try apply ord_set; split; auto.
          * apply bel_universe_set; apply dom_value; auto.
          * exists x0; split; auto; split; auto; split; auto.
            apply Property_Value; auto. }
    split; intros; auto.
    generalize (classic (x ∈ dom(En_f' g))); intro; destruct H2.
    + apply Axiom_Scheme in H2; destruct H2, H3; apply Axiom_SchemeP in H3.
      destruct H2, H3, H4, H5 as [h [H5 [H6 [H7 H8]]]].
      assert (h ⊂ En_f' g).
      { double H5; unfold Subclass; intros; unfold Function, Relation in H9.
        destruct H9 as [H9 _]; double H10; apply H9 in H11.
        destruct H11 as [a [b H11]]; rewrite H11 in *; clear H9 H11 z.
        apply Axiom_SchemeP; split; try Ens.
        double H10; apply Property_dom in H9.
        split; try apply Axiom_Scheme; Ens; split; Ens.
        eapply ord_bel_ord; eauto. }
      double H8; apply H9 in H10; double H8.
      apply Property_dom in H11; apply H7 in H11.
      double H8; apply Property_dom in H12; apply Property_dom in H8.
      apply Property_Value in H8; auto; apply Property_dom in H10.
      apply Property_Value in H10; auto; apply H9 in H8.
      assert (h [x] = (En_f' g) [x]). { eapply H; eauto. }
      rewrite <- H13; clear H13.
      assert (h | (x) = En_f' g | (x)).
      { apply Axiom_Extent.
        split; intros; apply Axiom_Scheme in H13; destruct H13, H14.
        - apply Axiom_Scheme; repeat split; auto.
        - apply Axiom_Scheme; repeat split; auto; rewrite fun_set_eq; auto.
          PP H15 a b; apply Axiom_SchemeP in H16.
          apply Axiom_SchemeP; split; auto.
          destruct H16, H17; assert (a ∈ dom(h)). { eapply lem_fun_ord_dom_value_res_eq; eauto. }
          apply Property_Value in H19; auto; apply H9 in H19; eapply H; eauto. }
      rewrite <- H13; auto.
    + generalize H2; intro; apply dom_value in H2; auto.
      rewrite (lem_fun_ord_dom_value_res_eq' _ _ H H0 H1 H3).
      generalize (classic (En_f' g ∈ dom(g))); intro; destruct H4.
      * generalize ord_not_set_R; intro; destruct H5 as [H5 _].
        apply ord_well_order in H5; unfold WellOrdered in H5; destruct H5.
        assert ((R ~ dom(En_f' g)) ⊂ R /\ (R ~ dom(En_f' g)) ≠ Φ).
        { split; try (red; intros; apply Axiom_Scheme in H7; tauto).
          intro; generalize (ord_sec_R _ H0); intro.
          unfold Section in H8; destruct H8.
          apply Property_Φ in H8; apply H8 in H7.
          rewrite <- H7 in H3; contradiction. }
        apply H6 in H7; destruct H7 as [y H7].
        assert (((En_f' g) ∪ [[y,g[En_f' g]]]) ⊂ (En_f' g)).
        { unfold Subclass; intros.
          apply Axiom_Scheme in H8; destruct H8, H9; auto.
          assert (Ensemble ([y, g [En_f' g]])).
          { destruct H7; AssE y; apply dom_value in H4.
            apply bel_universe_set in H4; apply ord_set; tauto. }
          apply Axiom_Scheme in H9; destruct H9.
          rewrite H11; try apply bel_universe_set; auto.
          apply Axiom_SchemeP; split; auto; split.
          - unfold FirstMember in H7; destruct H7.
            apply Axiom_Scheme in H7; tauto.
          - exists ((En_f' g) ∪ [[y,g[En_f' g]]]).
            assert (Function (En_f' g ∪ [[y, g [En_f' g]]])).
            { unfold Function; split; intros.
              - unfold Relation; intros; apply Axiom_Scheme in H12.
                destruct H12, H13; try PP H13 a b; eauto.
                apply Axiom_Scheme in H13; destruct H13; apply bel_universe_set in H10.
                apply H14 in H10; eauto.
              - destruct H12; apply Axiom_Scheme in H12.
                destruct H12 as [_ H12].
                apply Axiom_Scheme in H13; destruct H13 as [_ H13].
                unfold FirstMember in H7; destruct H7.
                apply Axiom_Scheme in H7; destruct H7 as [_ [_ H7]].
                apply Axiom_Scheme in H7; destruct H7, H12, H13.
                + eapply H; eauto.
                + apply Axiom_Scheme in H13; destruct H13.
                  apply bel_universe_set in H10.
                  apply H16 in H10; apply ord_eq in H10;
                  destruct H10; try apply ord_set; auto; rewrite H10 in H12.
                  apply Property_dom in H12; contradiction.
                + apply Axiom_Scheme in H12; destruct H12.
                  apply bel_universe_set in H10.
                  apply H16 in H10; apply ord_eq in H10; destruct H10;
                  try apply ord_set; auto; rewrite H10 in H13.
                  apply Property_dom in H13; contradiction.
                + double H12; apply Axiom_Scheme in H12.
                  apply Axiom_Scheme in H13.
                  destruct H12, H13; double H10.
                  apply bel_universe_set in H10; apply H17 in H10.
                  apply bel_universe_set in H19; apply H18 in H19.
                  apply ord_eq in H10; destruct H10;
                  apply ord_set in H12; auto.
                  apply ord_eq in H19; destruct H19;
                  apply ord_set in H13; auto.
                  rewrite H20, H21; auto. }
            split; auto; split.
            + apply sec_R_ord; unfold Section; intros; split.
              * unfold Subclass; intros.
                apply Axiom_Scheme in H13; destruct H13, H14.
                apply Axiom_Scheme in H14; destruct H14, H15.
                -- apply Property_dom in H15; apply Axiom_Scheme.
                   split; Ens; eapply ord_bel_ord; eauto.
                -- apply Axiom_Scheme in H15; destruct H15.
                   apply bel_universe_set in H10.
                   apply H16 in H10; apply ord_eq in H10; destruct H10;
                   try apply ord_set; auto; destruct H7.
                   apply Axiom_Scheme in H7; rewrite H10; tauto.
              * split; try (apply ord_well_order; apply ord_not_set_R); intros.
                destruct H13, H14; apply Axiom_Scheme in H14; destruct H14, H16.
                apply Axiom_Scheme in H16; destruct H16, H17.
                -- apply Axiom_Scheme; split; Ens.
                   assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                   { apply Property_Value; auto; apply Property_dom in H17.
                     unfold Rrelation in H15; apply Axiom_SchemeP in H15.
                     destruct H15; eapply lem_fun_ord_dom_value_res_eq; eauto. }
                   exists ((En_f' g) [u]); apply Axiom_Scheme; split; Ens.
                -- assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                   { apply Property_Value; auto.
                     apply Axiom_Scheme in H17; destruct H17.
                     apply bel_universe_set in H10; apply H18 in H10.
                     apply ord_eq in H10;
                     destruct H10; try apply ord_set; auto.
                     subst v; unfold FirstMember in H7; destruct H7.
                     generalize (classic (u ∈ dom( En_f' g))); intro.
                     destruct H20; auto.
                     absurd (Rrelation u E y); auto; try apply H10.
                     apply Axiom_Scheme; repeat split; Ens.
                     apply Axiom_Scheme; split; Ens. }
                   apply Axiom_Scheme; split; Ens; exists ((En_f' g) [u]).
                   apply Axiom_Scheme; split; Ens.
            + split; intros.
              * apply Property_Value in H13; auto.
                apply Axiom_Scheme in H13; destruct H13, H14.
                -- apply Axiom_SchemeP in H14; destruct H14, H15.
                   destruct H16 as [h [H16 [H17 [H18 H19]]]].
                   double H19; apply Property_dom in H20.
                   rewrite fun_set_eq in H19; auto.
                   apply Axiom_SchemeP in H19; destruct H19.
                   assert (h ⊂ En_f' g).
                   { unfold Subclass; intros; double H16.
                     unfold Function, Relation in H23; destruct H23 as [H23 _].
                     double H22; apply H23 in H24; destruct H24 as [a [b H24]].
                     rewrite H24 in *; clear H23 H24; apply Axiom_SchemeP.
                     split; try Ens; double H22; apply Property_dom in H23.
                     split; try apply Axiom_Scheme; Ens.
                     split; try Ens; eapply ord_bel_ord; eauto. }
                   assert ((En_f' g ∪ [[y, g[En_f' g]]])|(z0) = En_f' g|(z0)).
                   { unfold Restriction; rewrite inter_com; rewrite union_dist.
                     assert ((z0) × μ ∩ [[y, g [En_f' g]]] = Φ).
                     { apply Axiom_Extent; split; intros.
                       - apply Axiom_Scheme in H23; destruct H23, H24; auto.
                         PP H24 a b; apply Axiom_SchemeP in H26.
                         destruct H26, H27.
                         apply Axiom_Scheme in H25; destruct H25.
                         apply bel_universe_set in H10; apply H29 in H10.
                         apply ord_eq in H10; apply ord_set in H25; auto.
                         destruct H10; rewrite H10 in H27.
                         assert (y ∈ dom( h)).   { eapply lem_fun_ord_dom_value_res_eq; eauto. }
                         apply Property_Value in H31; auto.
                         apply H22 in H31; apply Property_dom in H31.
                         unfold FirstMember in H7; destruct H7.
                         apply Axiom_Scheme in H7; destruct H7, H33.
                         apply Axiom_Scheme in H34; destruct H34; contradiction.
                       - generalize (not_bel_zero z1); contradiction. }
                     rewrite H23, union_com, zero_union; apply inter_com. }
                   rewrite H21, H23.
                   assert (h | (z0) = En_f' g | (z0)).
                   { apply Axiom_Extent; split; intros.
                     - apply Axiom_Scheme in H24; destruct H24, H25.
                       apply Axiom_Scheme; repeat split; auto.
                     - apply Axiom_Scheme in H24; destruct H24, H25.
                       apply Axiom_Scheme.
                       repeat split; auto; rewrite fun_set_eq; auto.
                       PP H26 a b; apply Axiom_SchemeP in H27.
                       apply Axiom_SchemeP.
                       split; auto; destruct H27 as [_ [H27 _]].
                       assert (a ∈ dom(h)). { eapply lem_fun_ord_dom_value_res_eq; eauto. }
                       apply Property_Value in H28; auto; apply H22 in H28.
                       eapply H; eauto. }
                   rewrite <- H24; auto.
                -- apply Axiom_Scheme in H14; destruct H14.
                   double H10; apply bel_universe_set in H10; apply H15 in H10.
                   apply ord_eq in H10; apply ord_set in H13; auto.
                   destruct H10; subst z0; rewrite H17.
                   assert ((En_f' g ∪ [[y, g [En_f' g]]])|(y) = En_f' g|(y)).
                   { apply Axiom_Extent; split; intros.
                     - apply Axiom_Scheme in H10; destruct H10, H18.
                       apply Axiom_Scheme in H18; destruct H18, H20.
                       + apply Axiom_Scheme; tauto.
                       + PP H19 a b; apply Axiom_SchemeP in H21.
                         destruct H21, H22.
                         apply Axiom_Scheme in H20; destruct H20.
                         apply bel_universe_set in H16; apply H24 in H16.
                         apply ord_eq in H16; apply ord_set in H21; auto.
                         destruct H16; rewrite H16 in H22.
                         generalize (notin_fix y); intro; contradiction.
                     - unfold Restriction; rewrite inter_com, union_dist.
                       apply Axiom_Scheme.
                       split; Ens; left; rewrite inter_com; Ens. }
                   rewrite H10; unfold FirstMember in H7; destruct H7.
                   apply Axiom_Scheme in H7; destruct H7, H19.
                   apply Axiom_Scheme in H20; destruct H20.
                   rewrite lem_fun_ord_dom_value_res_eq'; auto.
              * apply Axiom_Scheme; split; Ens; right.
                apply Axiom_Scheme; split; Ens. }
        unfold FirstMember in H7; destruct H7.
        assert (y ∈ dom(En_f' g ∪ [[y, g [En_f' g]]])).
        { apply Axiom_Scheme; split; Ens; exists g [En_f' g].
          assert (Ensemble ([y, g [En_f' g]])).
          { apply ord_set; split; Ens.
            apply dom_value in H4; apply bel_universe_set; auto. }
          apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; auto. }
        apply Axiom_Scheme in H7; destruct H7, H11; apply Axiom_Scheme in H12.
        destruct H12; elim H13; apply Axiom_Scheme in H10; destruct H10, H14.
        apply H8 in H14; apply Property_dom in H14; auto.
      * apply dom_value in H4; rewrite H2, H4; auto.
Qed.

Lemma lem_fun_ord_dom_value_res_eq'' : forall f h,
  Function f -> Function h -> h ⊂ f -> f | (dom(h)) = h.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H2; destruct H2, H3.
    PP H4 a b; apply Axiom_SchemeP in H5; destruct H5, H6; double H3.
    rewrite fun_set_eq; rewrite fun_set_eq in H3; auto.
    apply Axiom_SchemeP in H3; destruct H3.
    apply Axiom_SchemeP; split; Ens; rewrite H9 in *.
    apply Property_Value in H6; auto.
    apply H1 in H6; eapply H; eauto.
  - apply Axiom_Scheme; repeat split; Ens.
    rewrite fun_set_eq in H2; auto.
    PP H2 a b; rewrite <- fun_set_eq in H3; auto.
    apply Axiom_SchemeP; repeat split; Ens.
    + apply Property_dom in H3; auto.
    + AssE [a,b]; apply ord_set in H4.
      apply bel_universe_set; tauto.
Qed.

Lemma lem_fun_ord_dom_value_res_eq''' : forall h, Function h -> h | (dom(h)) = h.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; tauto.
  - apply Axiom_Scheme; repeat split; Ens.
    rewrite fun_set_eq in H0; auto.
    PP H0 a b; rewrite <- fun_set_eq in H1; auto.
    apply Axiom_SchemeP; repeat split; Ens.
    + apply Property_dom in H1; auto.
    + AssE [a,b]; apply ord_set in H2.
      apply bel_universe_set; tauto.
Qed.

Lemma lem_fun_ord_dom_value_res_eq'''' : forall f g h,
  Function f -> Function h -> Ordinal dom(f) ->
  Ordinal dom( h)-> (forall x, Ordinal_Number x -> f [x] = g [f | (x)]) ->
  (forall x, Ordinal_Number x -> h [x] = g [h | (x)]) -> h ⊂ f -> h = f.
Proof.
  intros.
  generalize (ord_bel_eq _ _ (Lemma_xy _ _ H1 H2)); intro.
  destruct H6 as [H8 | [H6 | H6]].
  - apply Property_Value in H8; auto.
    apply H5 in H8; apply Property_dom in H8.
    apply notin_fix in H8; elim H8.
  - assert (Ordinal_Number dom(h)).
    { unfold Ordinal_Number; apply Axiom_Scheme; split; Ens. }
    double H7; apply H3 in H7; apply H4 in H8.
    rewrite lem_fun_ord_dom_value_res_eq'' in H7; rewrite lem_fun_ord_dom_value_res_eq''' in H8; auto.
    apply dom_value in H6; rewrite H7 in H6.
    generalize (notin_fix dom(h)); intro.
    apply dom_value in H9; rewrite H8 in H9.
    rewrite H9 in H6; apply notin_fix in H6; elim H6.
  - apply sub_eq; split; auto.
    unfold Subclass; intros.
    rewrite fun_set_eq; rewrite fun_set_eq in H7; auto.
    PP H7 a b; double H8; rewrite <- fun_set_eq in H8; auto.
    apply Axiom_SchemeP in H9; destruct H9.
    apply Axiom_SchemeP; split; auto; rewrite H10 in *.
    assert ([a,h[a]] ∈ h).
    { apply Property_Value; auto.
      apply Property_dom in H8; rewrite <- H6; auto. }
    apply H5 in H11; eapply H; eauto.
Qed.

Theorem fun_ord_dom_value_res_eq' :  forall g,
  forall f, Function f /\ Ordinal dom(f) /\
  (forall x, Ordinal_Number x -> f [x] = g [f | (x)]) ->
  forall h, Function h /\ Ordinal dom(h) /\
  (forall x, Ordinal_Number x -> h [x] = g [h | (x)]) -> f = h.
Proof.
  intros; destruct H, H0, H1, H2.
  assert (forall u, u ∈ dom(f) -> f [u] = g [f | (u)]); intros.
  { apply H3; unfold Ordinal_Number; apply Axiom_Scheme; split; Ens.
    apply ord_bel_ord with (x:= dom(f)); auto. }
  assert (forall u, u ∈ dom(h) -> h [u] = g [h | (u)]); intros.
  { apply H4; unfold Ordinal_Number; apply Axiom_Scheme; split; Ens.
    apply ord_bel_ord with (x:= dom(h)); auto. }
  generalize (fun_ord_res_sub f h g H H1 H5 H0 H2 H6); intro; destruct H7.
  - symmetry; eapply lem_fun_ord_dom_value_res_eq''''; eauto.
  - eapply lem_fun_ord_dom_value_res_eq''''; eauto.
Qed.

Hint Resolve fun_ord_dom_value_res_eq : set.


End Ord.

Export Ord.

