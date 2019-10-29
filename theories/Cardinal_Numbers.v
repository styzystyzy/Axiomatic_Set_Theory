Require Export Choice_Axiom.

(* CARDINAL NUMBERS *)

Module Cardinal.

(* 144 Definition  x ≈ y if and only if there is a 1_1 function f with
   domain f = x and range f = y. *)

Definition Equivalent x y : Prop :=
  exists f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.

Notation "x ≈ y" := (Equivalent x y) (at level 70).

Hint Unfold Equivalent : set.


(* 145 Theorem  x ≈ x. *)

Theorem equiv_fix : forall x, x ≈ x.
Proof.
  intros.
  unfold Equivalent.
  exists (\{\ λ u v, u ∈ x /\ u = v \}\); split.
  - unfold Function1_1; split.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H a b; Ens.
      * destruct H; apply Axiom_SchemeP in H.
        apply Axiom_SchemeP in H0; destruct H, H0, H1, H2.
        rewrite <- H3, <- H4; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H a b; Ens.
      * unfold Inverse in H; destruct H; apply Axiom_SchemeP in H.
        apply Axiom_SchemeP in H0; destruct H, H0.
        apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
        destruct H1, H2, H3, H4; rewrite H5, H6; auto.
   - split.
     + apply Axiom_Extent; split; intros.
       * unfold Domain in H; apply Axiom_Scheme in H; destruct H, H0.
         apply Axiom_SchemeP in H0; apply H0.
       * unfold Domain; apply Axiom_Scheme; split; Ens.
         exists z; apply Axiom_SchemeP; repeat split; auto.
         apply ord_set; split; Ens.
     + apply Axiom_Extent; split; intros.
       * unfold Range in H; apply Axiom_Scheme in H; destruct H, H0.
         apply Axiom_SchemeP in H0; destruct H0, H1.
         rewrite H2 in H1; auto.
       * unfold Range; apply Axiom_Scheme; split; Ens.
         exists z; apply Axiom_SchemeP; repeat split; auto.
         apply ord_set; split; Ens.
Qed.

Hint Resolve equiv_fix : set.


(* 146 Theorem  If x ≈ y, then y ≈ x. *)

Theorem equiv_com : forall x y, x ≈ y -> y ≈ x.
Proof.
  intros.
  unfold Equivalent in H; destruct H as [f H], H, H0.
  unfold Equivalent; exists f⁻¹; split.
  - unfold Function1_1 in H; destruct H.
    unfold Function1_1; split; try rewrite rel_inv_fix; try apply H; auto.
  - unfold Inverse; split.
    + unfold Domain; apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H2; destruct H2, H3.
        apply Axiom_SchemeP in H3; destruct H3.
        apply Property_ran in H4; rewrite H1 in H4; auto.
      * apply Axiom_Scheme; split; Ens.
        rewrite <- H1 in H2; unfold Range in H2.
        apply Axiom_Scheme in H2; destruct H2, H3.
        exists (x0); apply Axiom_SchemeP; split; auto.
        apply ord_set; AssE ([x0,z]).
        apply ord_set in H4; destruct H4; Ens.
    + unfold Range; apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H2; destruct H2, H3.
        apply Axiom_SchemeP in H3; destruct H3.
        apply Property_dom in H4; rewrite H0 in H4; auto.
      * apply Axiom_Scheme; split; Ens.
        rewrite <- H0 in H2; unfold Domain in H2.
        apply Axiom_Scheme in H2; destruct H2, H3.
        exists (x0); apply Axiom_SchemeP; split; auto.
        apply ord_set; AssE ([z,x0]).
        apply ord_set in H4; destruct H4; Ens.
Qed.

Hint Resolve equiv_com : set.


(* 147 equiv_tran : If x ≈ y and y ≈ z, then x ≈ z. *)

Theorem equiv_tran : forall x y z,
  x ≈ y -> y ≈ z -> x ≈ z.
Proof.
  intros.
  unfold Equivalent in H, H0; unfold Equivalent.
  destruct H as [f1 H], H0 as [f2 H0], H, H0, H1, H2.
  exists (\{\λ u v, exists w, [u,w] ∈ f1 /\ [w,v] ∈ f2\}\); split.
  - unfold Function1_1; unfold Function1_1 in H, H0.
    destruct H, H0; split.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H7 a b; Ens.
      * destruct H7; apply Axiom_SchemeP in H7; destruct H7, H9.
        apply Axiom_SchemeP in H8; destruct H8, H10; clear H7 H8.
        unfold Function in H, H0; destruct H9, H10, H, H0.
        add ([x0,x2] ∈ f1) H7; apply H11 in H7; rewrite H7 in H8.
        add ([x2,z0] ∈ f2) H8; apply H12 in H8; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H7 a b; Ens.
      * unfold Inverse in H7; destruct H7; apply Axiom_SchemeP in H7.
        apply Axiom_SchemeP in H8; destruct H7, H8; clear H7 H8.
        apply Axiom_SchemeP in H9; destruct H9, H8.
        apply Axiom_SchemeP in H10; destruct H10, H10; clear H7 H9.
        unfold Function in H5, H6; destruct H8, H10, H5, H6.
        assert ([x0,x1] ∈ f2⁻¹ /\ [x0,x2] ∈ f2⁻¹).
        { unfold Inverse; split.
          - apply Axiom_SchemeP; split; auto; AssE [x1,x0].
            apply ord_set in H13; destruct H13.
            apply ord_set; split; auto.
          - apply Axiom_SchemeP; split; auto; AssE [x2,x0].
            apply ord_set in H13; destruct H13.
            apply ord_set; split; auto. }
        apply H12 in H13; rewrite H13 in H7; clear H8 H10 H12 H13.
        assert ([x2,y0] ∈ f1⁻¹ /\ [x2,z0] ∈ f1⁻¹).
        { unfold Inverse; split.
          - apply Axiom_SchemeP; split; auto; AssE [y0,x2].
            apply ord_set in H8; destruct H8.
            apply ord_set; split; auto.
          - apply Axiom_SchemeP; split; auto; AssE [z0,x2].
            apply ord_set in H8; destruct H8.
            apply ord_set; split; auto. }
        apply H11 in H8; auto.
  - rewrite <- H1, <- H4; split.
    + apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H5; destruct H5, H6.
        apply Axiom_SchemeP in H6; destruct H6, H7, H7.
        apply Property_dom in H7; auto.
      * apply Axiom_Scheme; split; Ens; apply Axiom_Scheme in H5.
        destruct H5, H6; double H6; apply Property_ran in H7.
        rewrite H3 in H7; rewrite <- H2 in H7; apply Axiom_Scheme in H7.
        destruct H7, H8; exists x1; apply Axiom_SchemeP; split; Ens.
        AssE [z0,x0]; AssE [x0,x1]; apply ord_set in H9.
        apply ord_set in H10; destruct H9, H10.
        apply ord_set; split; auto.
    + apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H5; destruct H5, H6.
        apply Axiom_SchemeP in H6; destruct H6, H7, H7.
        apply Property_ran in H8; auto.
      * apply Axiom_Scheme; split; Ens; apply Axiom_Scheme in H5.
        destruct H5, H6; double H6; apply Property_dom in H7.
        rewrite H2 in H7; rewrite <- H3 in H7; apply Axiom_Scheme in H7.
        destruct H7, H8; exists x1; apply Axiom_SchemeP; split; Ens.
        AssE [x0,z0]; AssE [x1,x0]; apply ord_set in H9.
        apply ord_set in H10; destruct H9, H10.
        apply ord_set; split; auto.
Qed.

Hint Resolve equiv_tran : set.


(* 148 Definition148  x is a cardinal number if and onlu if x is a ordinal
   number and, if y∈R and y≺x, then it is false that x ≈ y. *)

Definition Cardinal_Number x : Prop :=
  Ordinal_Number x /\ (forall y, y∈R -> y ≺ x -> ~ (x ≈ y)).

Hint Unfold Cardinal_Number : set.


(* 149 Definition  C = {x : x is a cardinal number}. *)

Definition C : Class := \{ λ x, Cardinal_Number x \}.

Hint Unfold C : set.


(* 150 Theorem E well-orders C. *)

Theorem well_order_E : WellOrdered E C.
Proof.
  intros.
  unfold WellOrdered; split; intros.
  - unfold Connect; intros; destruct H; unfold C in H, H0.
    apply Axiom_Scheme in H; apply Axiom_Scheme in H0; destruct H, H0.
    unfold Cardinal_Number in H1, H2; destruct H1, H2; clear H3 H4.
    unfold Ordinal_Number, R in H1, H2; apply Axiom_Scheme in H1.
    apply Axiom_Scheme in H2; destruct H1, H2; add (Ordinal v) H3.
    clear H1 H2 H4; apply ord_bel_eq in H3; destruct H3.
    + left; unfold Rrelation, E; apply Axiom_SchemeP.
      split; try apply ord_set; auto.
    + destruct H1; auto; right; left; unfold Rrelation, E.
      apply Axiom_SchemeP; split; try apply ord_set; auto.
  - destruct H; assert (y ⊂ R).
    { unfold Subclass; intros; unfold Subclass in H.
      apply H in H1; unfold C in H1; apply Axiom_Scheme in H1.
      destruct H1; unfold Cardinal_Number in H2; destruct H2.
      unfold Ordinal_Number in H2; auto. }
    add (y ≠ Φ) H1; apply sub_noteq_firstmemb in H1; Ens.
Qed.

Hint Resolve well_order_E : set.


(* 151 Definition  P = { [x,y] : x ≈ y and y∈C }. *)

Definition P : Class := \{\ λ x y, x ≈ y /\ y ∈ C \}\.

Hint Unfold P : set.


(* 152 Theorem  P is a function, domain P = μ and range P = C. *)

Theorem card_fun : Function P /\ dom(P) = μ /\ ran(P) = C.
Proof.
  unfold P; repeat split; intros.
  - unfold Relation; intros; PP H a b; Ens.
  - destruct H; apply Axiom_SchemeP in H; apply Axiom_SchemeP in H0.
    destruct H, H0, H1, H2; apply equiv_com in H1.
    apply (equiv_tran _ _ z) in H1; auto; clear H H0 H2.
    unfold C in H3, H4; apply Axiom_Scheme in H3; destruct H3.
    apply Axiom_Scheme in H4; destruct H4.
    unfold Cardinal_Number in H0, H3; destruct H0, H3.
    unfold Ordinal_Number in H0, H3.
    assert (Ordinal y /\ Ordinal z).
    { unfold R in H0, H3; apply Axiom_Scheme in H0.
      apply Axiom_Scheme in H3; destruct H0, H3; split; auto. }
    apply ord_bel_eq in H6; destruct H6.
    + apply equiv_com in H1; apply H5 in H0; auto; try contradiction.
    + destruct H6; auto; apply H4 in H3; auto; try contradiction.
  - apply Axiom_Extent; split; intros; try apply bel_universe_set; Ens.
    apply bel_universe_set in H; double H; apply exist_fun1_ordnum in H0.
    destruct H0 as [f H0], H0, H1; apply Axiom_Scheme; split; auto.
    assert (WellOrdered E \{ λ x, x ≈ z /\ Ordinal x \}).
    { assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ R).
      { unfold Subclass; intros; apply Axiom_Scheme in H3.
        destruct H3, H4; apply Axiom_Scheme; split; auto. }
      apply (lem_order_pre_sec_sub _ E _) in H3; auto.
      apply ord_well_order; apply ord_not_set_R. }
    unfold WellOrdered in H3; destruct H3 as [H4 H3]; clear H4.
    assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ \{ λ x, x ≈ z /\ Ordinal x \}
            /\ \{ λ x, x ≈ z /\ Ordinal x \} ≠ Φ).
    { split; try unfold Subclass; auto.
      apply not_zero_exist_bel; exists dom(f); apply Axiom_Scheme.
      unfold Ordinal_Number, R in H2; apply Axiom_Scheme in H2; destruct H2.
      split; auto; split; auto; unfold Equivalent; exists f; auto. }
    apply H3 in H4; destruct H4; unfold FirstMember in H4; destruct H4.
    apply Axiom_Scheme in H4; destruct H4, H6.
    exists x; apply Axiom_SchemeP.
    repeat split; try apply ord_set; auto.
    + apply equiv_com; unfold Equivalent; Ens.
    + unfold C; apply Axiom_Scheme; split; auto.
      unfold Cardinal_Number; split; intros.
      { unfold Ordinal_Number, R; apply Axiom_Scheme; auto. }
      { unfold Less in H9; unfold R in H8.
        apply Axiom_Scheme in H8; destruct H8; intro.
        assert (y ∈ \{ λ x,x ≈ z /\ Ordinal x \}).
        { apply Axiom_Scheme; split; auto; split; auto.
          apply equiv_com in H11; apply (equiv_tran _ x _); auto. }
        apply H5 in H12; apply H12; unfold Rrelation, E.
        apply Axiom_SchemeP; split; try apply ord_set; auto. }
  - unfold Range; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H; destruct H, H0.
      apply Axiom_SchemeP in H0; apply H0.
    + apply Axiom_Scheme; split; Ens; exists z; apply Axiom_SchemeP.
      repeat split; try apply ord_set; Ens.
      apply equiv_fix.
Qed.

Hint Resolve card_fun : set.


(* A corollary of definition151. *)

Corollary Property_PClass : forall x, Ensemble x -> P [x] ∈ C.
Proof.
  intros.
  generalize card_fun; intros; destruct H0, H1.
  apply bel_universe_set in H; rewrite <- H1 in H.
  apply Property_Value in H; auto.
  apply Property_ran in H; rewrite H2 in H; auto.
Qed.

Hint Resolve Property_PClass : set.


(* 153 Theorem  If x is a set, then P[x] ≈ x. *)

Theorem card_equiv : forall x, Ensemble x -> P[x] ≈ x.
Proof.
  intros.
  generalize card_fun; intros; destruct H0, H1.
  apply bel_universe_set in H; rewrite <- H1 in H.
  apply Property_Value in H; auto.
  unfold P at 2 in H; apply Axiom_SchemeP in H.
  apply equiv_com; apply H.
Qed.

Hint Resolve card_equiv : set.


(* 154 Theorem  If x and y are sets, then x ≈ y if and onlf if P[x] = P[y]. *)

Theorem card_eq : forall x y,
  Ensemble x /\ Ensemble y -> (P[x] = P[y] <-> x ≈ y).
Proof.
  intros; double H; destruct H, H0.
  apply card_equiv in H0; apply card_equiv in H2; split; intros.
  - rewrite H3 in H0; apply equiv_com in H0.
    apply (equiv_tran _ P[y] _); auto.
  - generalize card_fun; intros; destruct H4, H5.
    double H; apply bel_universe_set in H; apply bel_universe_set in H1.
    rewrite <- H5 in H, H1; apply Property_Value in H; auto.
    apply Property_Value in H1; auto; apply Property_ran in H1.
    rewrite H6 in H1; apply equiv_com in H2.
    assert ([x, P [y]] ∈ P).
    { unfold P at 2; apply Axiom_SchemeP; split.
      - apply ord_set; split; Ens.
      - split; try apply (equiv_tran _ y _); auto. }
    unfold Function in H4; apply H4 with (x:=x); auto.
Qed.

Hint Resolve card_eq : set.


(* 155 Theorem  P[ P[ x ] ] = P[ x ]. *)

Lemma card_fix : forall x, x ∈ C -> Ensemble x -> P[x] = x.
Proof.
  intros.
  double H0; apply Property_PClass in H1; AssE P[x].
  unfold C in H, H1; apply Axiom_Scheme in H; apply Axiom_Scheme in H1.
  clear H0 H2; destruct H, H1, H0, H2.
  apply card_equiv in H; unfold Ordinal_Number in H0, H2.
  double H0; double H2; unfold R in H5, H6; apply Axiom_Scheme in H5.
  apply Axiom_Scheme in H6; destruct H5, H6; add (Ordinal P[x]) H7.
  clear H1 H5 H6 H8; apply ord_bel_eq in H7; destruct H7.
  + apply H4 in H1; auto; contradiction.
  + symmetry; destruct H1; auto; apply H3 in H1; auto.
    apply equiv_com in H; contradiction.
Qed.

Theorem card_eq_inv : forall x, P[P[x]] = P[x].
Proof.
  intros.
  generalize card_fun; intros; destruct H, H0.
  generalize (classic (Ensemble x)); intros; destruct H2.
  - apply Property_PClass in H2; AssE P[x].
    apply card_fix in H2; auto.
  - generalize (classic (x ∈ dom(P))); intros; destruct H3.
    + rewrite H0 in H3; apply bel_universe_set in H3; contradiction.
    + apply dom_value in H3; rewrite H3.
      generalize (classic (μ ∈ dom(P))); intros; destruct H4.
      * generalize universe_notset; intros; elim H5; Ens.
      * apply dom_value in H4; rewrite H4; auto.
Qed.

Hint Resolve card_fix card_eq_inv : set.


(* 156 Theorem  x∈C if and only if x is a set and P[x] = x. *)

Theorem card_iff_eq : forall x,
  (Ensemble x /\ P[x] = x) <-> x∈C.
Proof.
  intros; split; intros.
  - destruct H; apply Property_PClass in H.
    rewrite H0 in H; auto.
  - AssE x; apply card_fix in H; auto.
Qed.

Hint Resolve card_iff_eq : set.


(* 157 Theorem  If y∈R and x⊂y, then P(x)≼y. *)

Theorem card_int_le : forall x y,
  y ∈ R /\ x ⊂ y -> P[x] ≼ y.
Proof.
  intros; destruct H.
  unfold R in H; apply Axiom_Scheme in H; destruct H.
  assert (WellOrdered E x /\ WellOrdered E R).
  { split; try (apply ord_well_order; apply ord_not_set_R).
    apply ord_well_order in H1; apply (lem_order_pre_sec_sub _ _ y); auto. }
  assert (Ensemble x /\ ~ Ensemble R).
  { split; try apply ord_not_set_R; apply sub_set in H0; Ens. }
  destruct H3; apply well_order_pre_set in H2; auto; clear H4.
  destruct H2 as [f H2], H2, H4; unfold Order_PXY in H4.
  destruct H4, H6, H7, H8; apply order_pre_fun1_inv in H7; destruct H7.
  unfold Function1_1 in H7; destruct H7 as [H11 H7]; clear H11.
  generalize (Property_F11 f); intros; destruct H11.
  assert (forall u, u ∈ x -> f[u] ≼ u).
  { intros; rewrite <- H5 in H13; double H13.
    apply Property_Value in H14; auto; apply Property_ran in H14.
    assert (Ordinal u /\ Ordinal f[u]).
    { rewrite H5 in H13; apply H0 in H13.
      add (u ∈ y) H1; apply ord_bel_ord in H1.
      unfold Section in H9; destruct H9; apply H9 in H14.
      unfold R in H14; apply Axiom_Scheme in H14; destruct H14; auto. }
    apply ord_bel_eq in H15; AssE ([u,f[u]]); try apply ord_set; Ens.
    assert (Section ran(f) E R /\ Order_Pr f⁻¹ E E /\ On f⁻¹ ran(f) /\To f⁻¹ R).
    { split; auto; split; auto; split; try (split; auto).
      rewrite H12, H5; unfold Subclass; intros.
      apply H0 in H17; add (z ∈ y) H1; apply ord_bel_ord in H1.
      unfold R; apply Axiom_Scheme; split; Ens. }
    apply sec_order_pre_not_rel with (u:= f[u]) in H17; auto; rewrite <- H12 in H13.
    apply dom_ran_inv''' in H13; try rewrite (rel_inv_fix f) in *; try apply H2; auto.
    rewrite <- H13 in H17; unfold LessEqual; destruct H15.
    - unfold Rrelation, E in H17; elim H17.
      apply Axiom_SchemeP; split; auto.
    - destruct H15; try symmetry in H15; tauto. }
  apply sec_R_ord in H9; clear H11 H12; double H0.
  try apply sub_set in H11; auto; apply card_equiv in H11.
  assert (x ≈ ran(f)). { unfold Equivalent; exists f; split; split; auto. }
  assert (ran(f) ≼ y /\ Ensemble ran(f)).
  { assert (ran(f) ⊂ y).
    { unfold Subclass; intros.
      unfold Range in H14; apply Axiom_Scheme in H14; destruct H14, H15.
      double H15; apply Property_dom in H16; double H16.
      apply Property_Value in H17; auto; add ([x0,f[x0]] ∈ f) H15.
      unfold Function in H2; apply H2 in H15; rewrite H15 in *.
      clear H15 H17; rewrite H5 in H16; double H16; apply H13 in H16.
      unfold LessEqual in H16; destruct H16.
      - apply H0 in H15; unfold Ordinal in H1; destruct H1.
        unfold full in H17; apply H17 in H15; apply H15 in H16; auto.
      - rewrite H16; apply H0 in H15; auto. }
    split; try apply sub_set with (x:= y); auto.
    generalize (classic (ran(f) = y)); intros.
    unfold LessEqual; destruct H15; try tauto.
    apply ord_sub_full_bel in H14; auto; unfold Ordinal in H9; apply H9. }
  destruct H14.
  assert (WellOrdered E \{ λ z, x ≈ z /\ Ordinal z \}).
  { assert (\{ λ z, x ≈ z /\ Ordinal z \} ⊂ R).
    { unfold Subclass; intros; apply Axiom_Scheme in H16.
      destruct H16, H17; apply Axiom_Scheme; split; auto. }
    apply (lem_order_pre_sec_sub _ E _) in H16; auto. }
  unfold WellOrdered in H16; destruct H16 as [H17 H16]; clear H17.
  assert (\{ λ z, x ≈ z /\ Ordinal z \} ⊂ \{ λ z, x ≈ z /\ Ordinal z \}
            /\ \{ λ z, x ≈ z /\ Ordinal z \} ≠ Φ).
  { split; try unfold Subclass; auto.
    apply not_zero_exist_bel; exists ran(f); apply Axiom_Scheme; split; auto. }
  apply H16 in H17; clear H16; destruct H17; unfold FirstMember in H16.
  destruct H16; apply Axiom_Scheme in H16; destruct H16, H18.
  assert (x0 ∈ C).
  { unfold C; apply Axiom_Scheme; split; auto.
    unfold Cardinal_Number; split; intros.
    - unfold Ordinal_Number, R; apply Axiom_Scheme; Ens.
    - intro; assert (y0 ∈ \{ λ z, x ≈ z /\ Ordinal z \}).
      { unfold R in H20; apply Axiom_Scheme in H20; destruct H20.
        apply Axiom_Scheme; split; auto; split; auto.
        apply equiv_tran with (y:= x0); auto. }
      apply H17 in H23; elim H23; clear H23.
      unfold Rrelation, E; apply Axiom_SchemeP; unfold Less in H21.
      split; auto; apply ord_set; Ens. }
  apply card_iff_eq in H20; clear H16; destruct H20.
  apply card_eq in H18; auto; rewrite H20 in H18; clear H20.
  assert (ran(f)∈ \{ λ z, x ≈ z /\ Ordinal z \}). { apply Axiom_Scheme; Ens. }
  apply H17 in H20; clear H17; rewrite H18; unfold LessEqual.
  add (Ordinal x0) H9; apply ord_bel_eq in H9; destruct H9 as [H9|[H9|H9]].
  - elim H20; unfold Rrelation, E; apply Axiom_SchemeP.
    split; try apply ord_set; Ens.
  - destruct H14.
    + unfold Ordinal in H1; destruct H1.
      unfold full in H17; apply H17 in H14; clear H17.
      unfold Subclass in H14; apply H14 in H9; auto.
    + rewrite H14 in H9; auto.
  - destruct H14; rewrite H9 in H14; auto.
Qed.

Hint Resolve card_int_le : set.


(* 158 Theorem  If y is a set and x⊂y, then P[x]≼P[y]. *)

Theorem card_le : forall x y,
  Ensemble y /\ x ⊂ y -> P[x] ≼ P[y].
Proof.
  intros; destruct H.
  assert (Ensemble x). { apply sub_set in H0; auto. }
  double H; apply card_equiv in H2.
  apply equiv_com in H2; unfold Equivalent in H2.
  destruct H2 as [f H2], H2, H3; double H.
  apply Property_PClass in H5; unfold C in H5.
  apply Axiom_Scheme in H5; destruct H5; unfold Cardinal_Number in H6.
  destruct H6; clear H7; unfold Ordinal_Number in H6.
  assert (ran(f|(x)) ⊂ P[y]).
  { rewrite <- H4; unfold Subclass; intros.
    unfold Range in H7; apply Axiom_Scheme in H7; destruct H7, H8.
    unfold Restriction in H8; apply bel_inter in H8; destruct H8.
    apply Property_ran in H8; auto. }
  add (ran(f|(x)) ⊂ P [y]) H6; apply card_int_le in H6.
  assert (x ≈ ran(f|(x))).
  { unfold Function1_1 in H2; destruct H2.
    unfold Equivalent; exists (f|(x)); split.
    - unfold Function1_1; split.
      + unfold Function; split; intros.
        * unfold Relation; intros; unfold Restriction in H9.
          apply bel_inter in H9; destruct H9; PP H10 a b; Ens.
        * destruct H9; unfold Restriction in H9, H10.
          apply bel_inter in H9; apply bel_inter in H10.
          destruct H9, H10; add ([x0,z] ∈ f) H9.
          unfold Function in H2; apply H2 in H9; auto.
      + unfold Function; split; intros.
        * unfold Relation; intros; PP H9 a b; Ens.
        * destruct H9; unfold Inverse in H9, H10.
          apply Axiom_SchemeP in H9; apply Axiom_SchemeP in H10.
          destruct H9, H10; unfold Restriction in H11, H12.
          apply bel_inter in H11; apply bel_inter in H12.
          destruct H11, H12; clear H13 H14.
          assert ([x0,y0] ∈ f⁻¹ /\ [x0,z] ∈ f⁻¹).
          { unfold Inverse; split; apply Axiom_SchemeP; Ens. }
          unfold Function in H8; apply H8 in H13; auto.
    - split; auto; apply Axiom_Extent; intros; split; intros.
      + unfold Domain in H9; apply Axiom_Scheme in H9; destruct H9, H10.
        unfold Restriction in H10; apply bel_inter in H10; destruct H10.
        unfold Cartesian in H11; apply Axiom_SchemeP in H11; apply H11.
      + unfold Domain; apply Axiom_Scheme; split; Ens.
        double H9; unfold Subclass in H0; apply H0 in H10.
        rewrite <- H3 in H10; apply Property_Value in H10; auto.
        exists f[z]; unfold Restriction; apply bel_inter; split; auto.
        unfold Cartesian; apply Axiom_SchemeP; repeat split; Ens.
        AssE [z,f[z]]; apply ord_set in H11; destruct H11.
        apply bel_universe_set; auto. }
  assert (Ensemble ran(f|(x))). { apply sub_set in H7; auto. }
  apply card_eq in H8; auto; rewrite <- H8 in H6; auto.
Qed.

Hint Resolve card_le : set.


(* 159 Theorem  If x and y are sets, u⊂x, v⊂y, x≈v, and y≈u, then x≈y. *)

Theorem Schroder_Bernstein_theorem : forall (x y: Class),
  Ensemble x /\ Ensemble y ->
  (forall u v, u ⊂ x /\ v ⊂ y -> x ≈ v /\ y ≈ u -> x ≈ y).
Proof.
  intros; destruct H0, H1; elim H; intros.
  assert (Ensemble x /\ Ensemble v).
  { split; apply sub_set in H2; auto. }
  assert (Ensemble y /\ Ensemble u).
  { split; apply sub_set in H0; auto. }
  apply card_eq in H; apply card_eq in H6.
  apply card_eq in H7; apply H; apply H6 in H1.
  apply H7 in H3; clear H H6 H7; double H4; double H5.
  add (u ⊂ x) H4; add (v ⊂ y) H6; clear H0 H2.
  apply card_le in H4; apply card_le in H6.
  rewrite <- H3 in H4; rewrite <- H1 in H6; clear H1 H3.
  apply Property_PClass in H; apply Property_PClass in H5.
  unfold C in H, H5; apply Axiom_Scheme in H; apply Axiom_Scheme in H5.
  destruct H, H5; unfold Cardinal_Number in H0, H2.
  destruct H0, H2; unfold Ordinal_Number, R in H0, H2.
  apply Axiom_Scheme in H0; apply Axiom_Scheme in H2; destruct H0, H2.
  clear H H0 H1 H2 H3 H5.
  assert (Ordinal P [x] /\ Ordinal P [y]). { auto. }
  assert (Ordinal P [y] /\ Ordinal P [x]). { auto. }
  apply ord_sub_iff_le in H; apply ord_sub_iff_le in H0; clear H7 H8.
  apply H in H6; apply H0 in H4; clear H H0.
  apply sub_eq; split; auto.
Qed.

Hint Resolve Schroder_Bernstein_theorem : set.


(* Schroeder-Bernstein Theorem (proof without AC) *)

(* Image Set *)

Definition Imgset f x := \{ λ u, exists v, v ∈ x /\ u = f[v] \}.

Hint Unfold Imgset : set.

Inductive Ind := | fir : Ind | next : Ind -> Ind.

Fixpoint C' x u g f (n: Ind) : Class :=
   match n with
      | fir => (x ~ u)
      | next p => Imgset g (Imgset f (C' x u g f p))
       end.

Lemma tj : forall a b f, Function1_1 f -> b ∈ ran(f) -> a = f⁻¹[b] -> b = f [a].
Proof.
  intros. pattern b.
  rewrite dom_ran_inv''' with (f:=f); try apply H; auto.
  rewrite H1; auto.
Qed.

Lemma tj0 : forall a b f, Function1_1 f -> a ∈ dom(f) -> b = f[a] -> a = f⁻¹[b].
Proof.
  intros. pattern a.
  rewrite tj with (f:=f⁻¹) (a:=b); auto.
  - destruct H; split; auto.
    rewrite rel_inv_fix; try apply H; auto.
  - rewrite <- dom_ran_inv; auto.
  - rewrite rel_inv_fix; try apply H; auto.
Qed.

Theorem Cantor_Bernstein_Schroeder : forall x y u v,
  Ensemble x -> Ensemble y -> u ⊂ x -> v ⊂ y -> x ≈ v -> y ≈ u -> x ≈ y.
Proof.
  intros; destruct H3 as [f H3], H3, H5, H4 as [g H4], H4, H7.
  set (C:= (C' x u g f)); set (CC:=  \{ λ u, exists n, u = C n \}).
  assert (forall z, z ∈ x -> ~ z ∈ (∪ CC) -> z ∈ (x ~ (∪ CC))) as G1; intros.
  { apply Axiom_Scheme; repeat split; Ens.
    apply Axiom_Scheme; split; Ens. }
  assert ((∪ CC) ⊂ x) as G2.
  { red; intros.
    apply Axiom_Scheme in H9; destruct H9, H10, H10.
    apply Axiom_Scheme in H11; destruct H11, H12; subst x0.
    clear H9 H11; generalize dependent z.
    induction x1; intros; unfold C in H10; simpl in H10.
    - apply Axiom_Scheme in H10; tauto.
    - apply Axiom_Scheme in H10; destruct H10, H10, H10.
      apply Axiom_Scheme in H10; destruct H10, H12, H12.
      apply IHx1 in H12; subst x0 x v y u z.
      apply Property_Value in H12; try apply H3.
      apply Property_ran in H12; apply H2 in H12.
      apply Property_Value in H12; try apply H4.
      apply Property_ran in H12; auto. }
  assert (forall z, z ∈ x -> ~ z ∈ (∪ CC) -> z ∈ ran( g)) as G3; intros.
  { rewrite H8; destruct (classic (z ∈ u)); auto.
    elim H10; apply Axiom_Scheme; split; Ens.
    exists (C fir); unfold C; simpl; split.
    - apply Axiom_Scheme; repeat split; Ens.
      apply Axiom_Scheme; split; Ens.
    - apply Axiom_Scheme; split.
      + apply sub_set with (x:=x); auto.
        red; intros; apply Axiom_Scheme in H12; tauto.
      + exists fir; auto. }
  exists \{\ λ p q, (p ∈ x) /\ ((p ∈ (∪CC) -> q = f[p]) /\ (p ∈ (x ~ (∪CC)) ->
  q = g⁻¹[p])) \}\.
  repeat split; intros.
  - red; intros; PP H9 a b; eauto.
  - destruct H9; apply Axiom_SchemeP in H9; destruct H9, H11, H12.
    apply Axiom_SchemeP in H10; destruct H10, H14, H15, (classic (x0 ∈ (∪ CC))).
    + rewrite H12, H15; auto.
    + rewrite H13, H16; auto.
  - red; intros; PP H9 a b; eauto.
  - destruct H9; apply Axiom_SchemeP in H9; destruct H9.
    apply Axiom_SchemeP in H10; destruct H10.
    apply Axiom_SchemeP in H11; apply Axiom_SchemeP in H12. 
    destruct H11, H13, H14, H12, H16, H17.
    destruct (classic (y0 ∈ (∪ CC))), (classic (z ∈ (∪ CC))).
    + apply H14 in H19; apply H17 in H20; subst x.
      apply tj0 in H19; apply tj0 in H20; auto.
      rewrite H19, H20; auto.
    + double H19; double H20; apply G1 in H20; auto.
      apply H14 in H19; apply H18 in H20.
      subst x; rewrite H19 in H20.
      apply G3 in H16; apply tj in H20; auto.
      elim H22; apply Axiom_Scheme; split; Ens.
      apply Axiom_Scheme in H21; destruct H21, H21, H21.
      apply Axiom_Scheme in H23; destruct H23, H24; subst x.
      exists (C (next x1)); split.
      * unfold C; simpl; apply Axiom_Scheme; split; Ens.
        exists f[y0]; split; auto; apply Axiom_Scheme; split; Ens.
        apply dom_value in H13; apply bel_universe_set; auto.
      * apply Axiom_Scheme; split; Ens; unfold C; simpl.
        apply sub_set with (x:= dom(f)); auto; red; intros.
        apply Axiom_Scheme in H24; destruct H24, H25, H25; subst z0.
        assert (x ∈ dom(g)).
        { destruct (classic (x ∈ dom(g))); auto.
          apply dom_value in H26; rewrite H26 in H24.
          destruct (universe_notset H24). }
        apply Property_Value in H26; try apply H4.
        apply Property_ran in H26.
        rewrite H8 in H26; auto.
    + double H19; double H20; apply G1 in H19; auto.
      apply H17 in H20; apply H15 in H19.
      subst x; rewrite H20 in H19.
      apply G3 in H13; apply tj in H19; auto.
      elim H21; apply Axiom_Scheme; split; Ens.
      apply Axiom_Scheme in H22; destruct H22, H22, H22.
      apply Axiom_Scheme in H23; destruct H23, H24; subst x.
      exists (C (next x1)); split.
      * unfold C; simpl; apply Axiom_Scheme; split; Ens.
        exists f[z]; split; auto; apply Axiom_Scheme; split; Ens.
        apply dom_value in H16; apply bel_universe_set; auto.
      * apply Axiom_Scheme; split; Ens; unfold C; simpl.
        apply sub_set with (x:= dom(f)); auto; red; intros.
        apply Axiom_Scheme in H24; destruct H24, H25, H25; subst z0.
        assert (x ∈ dom(g)).
        { destruct (classic (x ∈ dom(g))); auto.
          apply dom_value in H26; rewrite H26 in H24.
          destruct (universe_notset H24). }
        apply Property_Value in H26; try apply H4.
        apply Property_ran in H26.
        rewrite H8 in H26; auto.
    + double H13; double H16.
      apply G3 in H21; apply G3 in H22; auto.
      apply G1 in H19; apply G1 in H20; auto.
      apply H15 in H19; apply H18 in H20; auto.
      apply tj in H19; apply tj in H20; auto.
      rewrite H19, H20; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H9; destruct H9, H10.
      apply Axiom_SchemeP in H10; destruct H10; tauto.
    + apply Axiom_Scheme; split; Ens.
      destruct (classic (z ∈ (∪ CC))); subst x.
      * exists f[z]; apply Axiom_SchemeP.
        repeat split; intros; auto.
        { apply ord_set; split; Ens.
          apply bel_universe_set; apply dom_value; auto. }
        { apply Axiom_Scheme in H5; destruct H5, H11.
          apply Axiom_Scheme in H12; destruct H12; contradiction. }
      * exists g ⁻¹[z]; apply Axiom_SchemeP.
        repeat split; intros; auto; try tauto.
        apply ord_set; split; Ens; apply bel_universe_set; apply dom_value.
        rewrite <- dom_ran_inv', H8.
        destruct (classic (z ∈ u)); auto.
        elim H10; apply Axiom_Scheme; split; Ens.
        exists (C fir); split; apply Axiom_Scheme; repeat split; Ens.
        -- apply Axiom_Scheme; split; Ens.
        -- apply sub_set with dom(f); auto. 
           red; intros; apply Axiom_Scheme in H11; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H9; destruct H9, H10.
      apply Axiom_SchemeP in H10; destruct H10, H11, H12.
      destruct (classic (x0 ∈ (∪ CC))).
      * apply H12 in H14; subst z.
        apply H2; rewrite <- H6; rewrite <- H5 in H11.
        apply Property_Value in H11; try apply H3.
        apply Property_ran in H11; auto.
      * double H11; apply G1 in H11; apply G3 in H15; auto.
        apply H13 in H11; auto; rewrite dom_ran_inv' in H15.
        apply Property_Value in H15; try apply H4.
        apply Property_ran in H15; subst z.
        rewrite <- dom_ran_inv, H7 in H15; auto.
    + apply Axiom_Scheme; split; Ens.
      destruct (classic (z ∈ (Imgset f (∪ CC)))).
      * apply Axiom_Scheme in H10; destruct H10, H11, H11.
        exists x0; apply Axiom_SchemeP; repeat split; auto; intros.
        { apply ord_set; split; Ens. }
        { apply Axiom_Scheme in H13; destruct H13, H14.
          apply Axiom_Scheme in H15; destruct H15; contradiction. }
      * assert (g[z] ∈ ran(g)).
        { subst y; apply Property_Value in H9; try apply H4.
          apply Property_ran in H9; Ens. }
        assert (forall n, (C n) ⊂ (∪ CC)); intros.
        { apply bel_ele; apply Axiom_Scheme; split; Ens. 
          apply sub_set with (x:=x); auto.
          red; induction n; intros.
          - apply Axiom_Scheme in H12; tauto.
          - unfold C in H12; simpl in H12.
            apply Axiom_Scheme in H12; destruct H12, H13, H13.
            apply Axiom_Scheme in H13; destruct H13, H15, H15.
            apply IHn in H15; subst x z0 x0 v y u.
            apply Property_Value in H15; try apply H3.
            apply Property_ran in H15; apply H2 in H15.
            apply Property_Value in H15; try apply H4.
            apply Property_ran in H15; auto. }
        assert (~ g[z] ∈ (∪ CC)); try intro.
        { apply Axiom_Scheme in H13; destruct H13, H14, H14.
          apply Axiom_Scheme in H15; destruct H15, H16; subst x0 u.
          destruct x1.
          - apply Axiom_Scheme in H14; destruct H14, H14.
            apply Axiom_Scheme in H16; apply H16; auto.
          - unfold C in H14; simpl in H14.
            apply Axiom_Scheme in H14; destruct H14, H14, H14.
            apply Axiom_Scheme in H14; destruct H14, H17, H17.
            assert (z = x0) as G4.
            { rewrite dom_ran_inv''' with (f:=g⁻¹); try apply H4.
              - pattern z; rewrite dom_ran_inv''' with (f:=g⁻¹); try apply H4.
                + repeat rewrite rel_inv_fix; try apply H4; rewrite H16; auto.
                + rewrite rel_inv_fix; apply H4.
                + rewrite <- dom_ran_inv, H7; auto.
              - rewrite rel_inv_fix; apply H4.
              - rewrite <- dom_ran_inv; subst x x0 y v.
                apply H12 in H17; apply G2 in H17.
                apply Property_Value in H17; try apply H3.
                apply Property_ran in H17; auto. }
            subst x0 x; apply H10; apply Axiom_Scheme; split; Ens.
            exists x2; split; auto.
            apply Axiom_Scheme; split; Ens.
            exists (C x1); split; auto.
            apply Axiom_Scheme; split; eauto.
            apply sub_set with (x:=∪ CC); auto.
            apply sub_set with (x:=dom(f)); auto. }
        exists g[z]; apply Axiom_SchemeP; repeat split; intros.
        { apply ord_set; split; Ens. }
        { subst u x; auto. }
        { contradiction. }
        { pattern g at 2; rewrite <- rel_inv_fix; try apply H4.
          rewrite <- dom_ran_inv'''; auto; try apply H4.
          - rewrite rel_inv_fix; apply H4.
          - apply Property_Value' in H11; try apply H4.
            apply Property_dom in H11; rewrite <- dom_ran_inv; auto. }
Qed.

Hint Resolve Cantor_Bernstein_Schroeder : set.


(* 160 Theorem  If f is a function and f is a set, then P(range f)≼P(domain f). *)

Definition En_g f c : Class :=
  \{\ λ v u, v ∈ ran(f) /\ u = c[\{ λ x, v = f[x] \}] \}\.

Lemma lem_card_le_fun : forall c f y,
  Function f -> Ensemble dom(f) -> ChoiceFunction c -> dom( c) = μ ~ [Φ] ->
  y ∈ ran( f) -> \{ λ x, y = f[x] \} ∈ dom(c).
Proof.
  intros.
  unfold ChoiceFunction in H1; destruct H1.
  unfold Range in H3; apply Axiom_Scheme in H3; destruct H3, H5.
  rewrite H2; unfold Difference; apply bel_inter.
  assert (Ensemble (\{ λ x, y = f[x] \})).
  { apply sub_set with (x:= dom(f)); auto.
    unfold Subclass; intros; apply Axiom_Scheme in H6; destruct H6.
    rewrite H7 in H5; clear H7; apply Property_ran in H5.
    apply Property_Value' in H5; auto; apply Property_dom in H5; auto. }
  split; try apply bel_universe_set; auto.
  unfold Complement; apply Axiom_Scheme; split; auto.
  unfold NotIn; intro; unfold Singleton in H7.
  apply Axiom_Scheme in H7; clear H6; destruct H7.
  assert (Φ ∈ μ).
  { apply bel_universe_set; generalize Axiom_Infinity; intros.
    destruct H8; Ens; exists x0; apply H8. }
  apply H7 in H8; clear H7.
  assert (x ∈ \{ λ x, y = f [x] \}).
  { apply Axiom_Scheme; double H5; apply Property_dom in H7.
    split; Ens; apply Property_Value in H7; auto.
    unfold Function in H; apply H with (x:=x); Ens. }
  rewrite H8 in H7; generalize (not_bel_zero x); intros; contradiction.
Qed.

Theorem card_le_fun : forall f,
  Function f -> P[ran(f)] ≼ P[dom(f)].
Proof.
  intros.
  generalize (classic (Ensemble dom(f))); intros; destruct H0.
  - generalize Axiom_Choice; intros; destruct H1 as [c H1], H1.
    assert (Function1_1 (En_g f c)).
    { unfold Function1_1, Function; repeat split; intros.
      - unfold Relation; intros; PP H3 a b; Ens.
      - unfold En_g in H3; destruct H3.
        apply Axiom_SchemeP in H3; apply Axiom_SchemeP in H4.
        destruct H3, H4, H5, H6; rewrite H7, H8; auto.
      - unfold Relation; intros; PP H3 a b; Ens.
      - unfold Inverse, En_g in H3; destruct H3.
        apply Axiom_SchemeP in H3; apply Axiom_SchemeP in H4.
        destruct H3, H4; clear H3 H4; apply Axiom_SchemeP in H5.
        apply Axiom_SchemeP in H6; destruct H5, H6, H4, H6.
        assert (\{ λ x, y=f[x] \} ∈ dom(c) /\ \{ λ x, z=f[x] \} ∈ dom(c)).
        { split; apply lem_card_le_fun; auto. }
        destruct H9; apply H1 in H9; apply H1 in H10.
        rewrite <- H7 in H9; rewrite <- H8 in H10; apply Axiom_Scheme in H9.
        apply Axiom_Scheme in H10; destruct H9, H10; rewrite H11, H12; auto. }
    assert (ran(En_g f c) ⊂ dom(f)).
    { unfold Subclass; intros; unfold Range, En_g in H4; unfold Domain.
      apply Axiom_Scheme in H4; destruct H4, H5; apply Axiom_SchemeP in H5.
      destruct H5, H6; apply Axiom_Scheme; split; auto; exists f[z].
      assert (\{ λ x0, x = f [x0] \} ∈ dom(c)). { apply lem_card_le_fun; auto. }
      apply H1 in H8; rewrite <- H7 in H8.
      apply Axiom_Scheme in H8; destruct H8.
      rewrite H9 in H6; clear H9; apply Property_Value'; auto. }
    assert (Ensemble dom(f) /\ ran(En_g f c) ⊂ dom(f)); auto.
    apply card_le in H5; auto.
    assert (dom(En_g f c) ≈ ran(En_g f c)).
    { unfold Equivalent; exists (En_g f c); auto. }
    assert (dom(En_g f c) = ran(f)).
    { apply Axiom_Extent; split; intros.
      - unfold Domain, En_g in H7; apply Axiom_Scheme in H7.
        destruct H7, H8; apply Axiom_SchemeP in H8; apply H8.
      - unfold Domain, En_g; apply Axiom_Scheme; split; Ens.
        exists c[\{ λ x, z = f [x] \}]; apply Axiom_SchemeP; split; auto.
        apply ord_set; split; Ens; exists \{ λ x, z = f [x] \}.
        unfold ChoiceFunction in H1; apply H1; apply lem_card_le_fun; auto. }
    rewrite H7 in H6; clear H7.
    assert (Ensemble ran(f) /\ Ensemble ran(En_g f c)).
    { double H0; split; try apply Axiom_Substitution in H0; auto.
      apply sub_set with (x:= dom(f)); auto. }
    apply card_eq in H7; apply H7 in H6; clear H7; rewrite H6; auto.
  - generalize card_fun; intros; destruct H1, H2.
    generalize (classic (dom(f) ∈ dom(P))); intros; destruct H4.
    + rewrite H2 in H4; apply bel_universe_set in H4; contradiction.
    + apply dom_value in H4; rewrite H4; clear H4.
      generalize (classic (ran(f) ∈ dom(P))); intros; destruct H4.
      * rewrite H2 in H4; apply bel_universe_set in H4.
        apply Property_PClass in H4; unfold LessEqual.
        left; apply bel_universe_set; Ens.
      * apply dom_value in H4; rewrite H4; unfold LessEqual; tauto.
Qed.

Hint Resolve card_le_fun : set.


(* 161 Theorem  If x is a set, then P[x] ≺ P[pow(x)]. *)

Theorem card_lt_pow : forall x,
  Ensemble x -> P[x] ≺ P[ pow(x) ].
Proof.
  intros.
  assert (x ≈ \{ λ v, exists u, u∈x /\ v = [u] \}).
  { unfold Equivalent; exists \{\ λ u v, u∈x /\ v = [u] \}\.
    repeat split; auto; unfold Relation; intros; try PP H0 a b; Ens.
    - destruct H0; apply Axiom_SchemeP in H0; apply Axiom_SchemeP in H1.
      destruct H0, H1, H2, H3; rewrite H4, H5; auto.
    - destruct H0; apply Axiom_SchemeP in H0; apply Axiom_SchemeP in H1.
      destruct H0, H1; apply Axiom_SchemeP in H2; apply Axiom_SchemeP in H3.
      clear H0 H1; destruct H2, H3, H1, H3; rewrite H4 in H5.
      assert (y∈[y]). { apply Axiom_Scheme; split; Ens. }
      rewrite H5 in H6; apply Axiom_Scheme in H6; destruct H6.
      apply H7; apply bel_universe_set; Ens.
    - apply Axiom_Extent; split; intros.
      + unfold Domain in H0; apply Axiom_Scheme in H0; destruct H0, H1.
        apply Axiom_SchemeP in H1; apply H1.
      + unfold Domain; apply Axiom_Scheme; split; Ens; exists [z].
        AssE z; apply sing_set in H1; apply Axiom_SchemeP.
        repeat split; try apply ord_set; Ens.
    - apply Axiom_Extent; split; intros.
      + unfold Range in H0; apply Axiom_Scheme in H0; destruct H0, H1.
        apply Axiom_SchemeP in H1; destruct H1, H2; apply Axiom_Scheme; Ens.
      + apply Axiom_Scheme in H0; destruct H0, H1, H1; unfold Range.
        apply Axiom_Scheme; split; auto; exists x0; apply Axiom_SchemeP.
        repeat split; try apply ord_set; Ens. }
  assert (Ensemble pow(x) /\ \{λ v, exists u, u∈x /\ v=[u]\} ⊂ pow(x)).
  { split; try apply pow_set in H; auto.
    unfold Subclass; intros; apply Axiom_Scheme in H1; destruct H1, H2, H2.
    rewrite H3 in *; clear H3; unfold PowerClass.
    apply Axiom_Scheme; split; auto.
    unfold Subclass; intros; apply Axiom_Scheme in H3; destruct H3.
    rewrite H4; try apply bel_universe_set; Ens. }
  assert (Ensemble x /\ Ensemble \{λ v, exists u, u∈x /\ v=[u]\}).
  { split; auto; destruct H1; apply sub_set in H2; auto. }
  apply card_le in H1; apply card_eq in H2; apply H2 in H0.
  rewrite <- H0 in H1; clear H0 H2; unfold LessEqual in H1.
  unfold Less; destruct H1; auto.
  assert (Ensemble x /\ Ensemble pow(x)).
  { split; auto; apply pow_set in H; auto. }
  apply card_eq in H1; apply H1 in H0; clear H1.
  unfold Equivalent in H0; destruct H0 as [f H0], H0, H1.
  assert (\{λ v, v ∈ x /\ v ∉ f[v]\} ∈ ran(f)).
  { assert (\{λ v, v ∈ x /\ v ∉ f[v]\} ⊂ x).
    { unfold Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    double H3; apply sub_set in H4; auto; rewrite H2.
    unfold PowerClass; apply Axiom_Scheme; split; auto. }
  unfold Range in H3; apply Axiom_Scheme in H3; destruct H3, H4 as [u H4].
  double H4; apply Property_dom in H5; unfold Function1_1 in H0.
  destruct H0; clear H6; double H5; apply Property_Value in H6; auto.
  rewrite H1 in H5; add ([u,f[u]] ∈ f) H4; apply H0 in H4; clear H6.
  generalize (classic (u ∈ f[u])); intros; destruct H6.
  - double H6; rewrite <- H4 in H7; apply Axiom_Scheme in H7.
    destruct H7, H8; contradiction.
  - elim H6; rewrite <- H4; apply Axiom_Scheme; Ens.
Qed.

Hint Resolve card_lt_pow : set.


(* 162 Theorem  C is not a set. *)

Theorem C_not_set : ~ Ensemble C.
Proof.
  intro.
  apply Axiom_Amalgamation in H; double H.
  apply pow_set in H0; try apply C.
  apply Property_PClass in H0.
  assert (Ensemble (∪C) /\ P[ pow( ∪C ) ] ⊂ ∪C).
  { split; auto; apply bel_ele in H0; apply H0. }
  apply card_le in H1; rewrite card_eq_inv in H1.
  double H; apply card_lt_pow in H2; unfold Less in H2.
  unfold LessEqual in H1; destruct H1.
  - apply Property_PClass in H; generalize well_order_E; intros.
    apply well_tran_asy in H3; destruct H3; unfold Asymmetric in H4.
    assert (P[∪C] ∈ C /\ P[pow(∪C)] ∈ C /\ Rrelation P[∪C] E P[pow(∪C)]).
    { repeat split; auto; unfold Rrelation, E.
      apply Axiom_SchemeP; split; try apply ord_set; Ens. }
    apply H4 in H5; apply H5; clear H4 H5.
    unfold Rrelation, E; apply Axiom_SchemeP.
    split; try apply ord_set; Ens.
  - rewrite H1 in H2.
    generalize (notin_fix P[∪C]); intros; contradiction.
Qed.

Hint Resolve C_not_set : set.


(* We divide the cardinals into two classes, the finite cardinals and the
   infinte cardinals. *)

(* 163 Theorem  If x∈W, y∈W and x+1≈y+1, then x≈y. *)

Ltac SplitEns := apply Axiom_Scheme; split; Ens.

Ltac SplitEnsP := apply Axiom_SchemeP; split; try apply ord_set; Ens.

Definition En_g' f x y : Class :=
  \{\ λ u v, [u,v] ∈ (f ~ ([[x,f[x]]] ∪ [[f⁻¹[y],y]])) \/
      [u,v] = [f⁻¹[y],f[x]] \/ [u,v] = [x,y] \}\.

Theorem equiv_plus_equiv : forall x y,
  x∈W -> y∈W -> (PlusOne x) ≈ (PlusOne y) -> x ≈ y.
Proof.
  intros.
  unfold Equivalent in H1; destruct H1 as [f H1], H1, H2.
  unfold Function1_1 in H1; destruct H1; unfold Equivalent.
  exists ((En_g' f x y) | (x)); repeat split; intros.
  - unfold Relation; intros; unfold Restriction in H5.
    apply bel_inter in H5; destruct H5; PP H6 a b; Ens.
  - destruct H5; unfold Restriction in H5, H6.
    apply bel_inter in H5; apply bel_inter in H6.
    destruct H5, H6; clear H8; unfold En_g' in H5, H6.
    apply Axiom_SchemeP in H5; apply Axiom_SchemeP in H6; destruct H5,H6.
    unfold Cartesian in H7; apply Axiom_SchemeP in H7; clear H5.
    destruct H7, H7; clear H10; destruct H8, H9.
    + unfold Difference in H8, H9; apply bel_inter in H8.
      apply bel_inter in H9; destruct H8, H9; clear H10 H11.
      unfold Function in H1; apply H1 with (x:= x0); auto.
    + destruct H9.
      * unfold Difference in H8; apply bel_inter in H8; destruct H8.
        unfold Complement in H10; apply Axiom_Scheme in H10; clear H5.
        destruct H10; elim H10; clear H10; apply bel_union.
        right; apply Axiom_Scheme; split; auto; intros; clear H10.
        apply ord_set in H6; apply ord_eq in H9; auto.
        destruct H9; clear H10; double H8; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H8.
        apply H1 in H8; clear H10; rewrite H9 in H8.
        rewrite <- dom_ran_inv''' in H8; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply bel_union; right.
        unfold Singleton; apply Axiom_Scheme; split; Ens.
      * apply ord_set in H6; apply ord_eq in H9; auto; destruct H9.
        rewrite H9 in H7; generalize (notin_fix x); contradiction.
    + destruct H8.
      * unfold Difference in H9; apply bel_inter in H9; destruct H9.
        unfold Complement in H10; apply Axiom_Scheme in H10; clear H6.
        destruct H10; elim H10; clear H10; apply bel_union.
        right; apply Axiom_Scheme; split; auto; intros; clear H10.
        apply ord_set in H5; apply ord_eq in H8; auto.
        destruct H8; clear H10; double H9; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H9.
        apply H1 in H9; clear H10; rewrite H8 in H9.
        rewrite <- dom_ran_inv''' in H9; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply bel_union; right.
        unfold Singleton; apply Axiom_Scheme; split; Ens.
      * apply ord_set in H5; apply ord_eq in H8; auto; destruct H8.
        rewrite H8 in H7; generalize (notin_fix x); contradiction.
    + apply ord_set in H5; apply ord_set in H6.
      destruct H8, H9; apply ord_eq in H8; apply ord_eq in H9; auto.
      * destruct H8, H9; rewrite H10, H11; auto.
      * destruct H9; rewrite H9 in H7.
        generalize (notin_fix x); intros; contradiction.
      * destruct H8; rewrite H8 in H7.
        generalize (notin_fix x); intros; contradiction.
      * destruct H8; rewrite H8 in H7.
        generalize (notin_fix x); intros; contradiction.
  - unfold Relation; intros; PP H5 a b; Ens.
  - destruct H5; unfold Inverse, Restriction in H5, H6.
    apply Axiom_SchemeP in H5; apply Axiom_SchemeP in H6; destruct H5, H6.
    apply bel_inter in H7; apply bel_inter in H8; destruct H7, H8.
    apply Axiom_SchemeP in H7; apply Axiom_SchemeP in H8; destruct H7, H8.
    unfold Cartesian in H9; apply Axiom_SchemeP in H9; clear H7.
    destruct H9, H9; clear H13; apply Axiom_SchemeP in H10; clear H8.
    destruct H10, H10; clear H13; destruct H11, H12.
    + unfold Difference in H11, H12; apply bel_inter in H11.
      apply bel_inter in H12; destruct H11, H12; clear H13 H14.
      assert ([x0,y0] ∈ f⁻¹ /\ [x0,z] ∈ f⁻¹).
      { unfold Inverse; split; apply Axiom_SchemeP; split; auto. }
      unfold Function in H4; apply H4 in H13; auto.
    + destruct H12.
      * unfold Difference in H11; apply bel_inter in H11; destruct H11.
        clear H13; apply ord_set in H8; apply ord_eq in H12; auto.
        destruct H12; rewrite H13 in *; double H11.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],y0] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply Axiom_SchemeP; split; auto;AssE [x,f[x]].
          apply ord_set in H15; destruct H15; apply ord_set; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H9; generalize (notin_fix x); contradiction.
      * unfold Difference in H11; apply bel_inter in H11; destruct H11.
        unfold Complement in H13; apply Axiom_Scheme in H13; clear H7.
        destruct H13; elim H13; clear H13; apply bel_union.
        right; apply Axiom_Scheme; split; auto; intros; clear H13.
        apply ord_set in H8; apply ord_eq in H12; auto.
        destruct H12; rewrite H13 in *; clear H6 H8 H12 H13.
        assert ([y,y0] ∈ f⁻¹). { apply Axiom_SchemeP; Ens. }
        double H6; apply Property_dom in H8; apply Property_Value in H8; auto.
        add ([y,y0] ∈ f⁻¹) H8; apply H4 in H8; rewrite H8; auto.
    + destruct H11.
      * unfold Difference in H12; apply bel_inter in H12; destruct H12.
        clear H13; apply ord_set in H7; apply ord_eq in H11; auto.
        destruct H11; rewrite H13 in *; double H12.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],z] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply Axiom_SchemeP; split; auto;AssE [x,f[x]].
          apply ord_set in H15; destruct H15; apply ord_set; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H10; generalize (notin_fix x); contradiction.
      * unfold Difference in H12; apply bel_inter in H12; destruct H12.
        unfold Complement in H13; apply Axiom_Scheme in H13; clear H8.
        destruct H13; elim H13; clear H13; apply bel_union.
        right; apply Axiom_Scheme; split; auto; intros; clear H13.
        apply ord_set in H7; apply ord_eq in H11; auto.
        destruct H11; rewrite H13 in *; clear H5 H7 H11 H13.
        assert ([y,z] ∈ f⁻¹). { apply Axiom_SchemeP; Ens. }
        double H5; apply Property_dom in H7; apply Property_Value in H7; auto.
        add ([y,z] ∈ f⁻¹) H7; apply H4 in H7; rewrite H7; auto.
    + apply ord_set in H7; apply ord_set in H8.
      destruct H11, H12; apply ord_eq in H11; apply ord_eq in H12; auto.
      * destruct H11, H12; rewrite H11, H12; auto.
      * destruct H12; rewrite H12 in H10.
        generalize (notin_fix x); intros; contradiction.
      * destruct H11; rewrite H11 in H9.
        generalize (notin_fix x); intros; contradiction.
      * destruct H12; rewrite H12 in H10.
        generalize (notin_fix x); intros; contradiction.
  - apply Axiom_Extent; split; intros.
    + unfold Domain in H5; apply Axiom_Scheme in H5; destruct H5, H6.
      unfold Restriction in H6; apply bel_inter in H6; destruct H6.
      unfold Cartesian in H7; apply Axiom_SchemeP in H7; apply H7.
    + unfold Domain; apply Axiom_Scheme; split; Ens.
      assert ([x,f[x]] ∈ f).
      { apply Property_Value; auto; rewrite H2; unfold PlusOne.
        apply bel_union; right; apply Axiom_Scheme; split; Ens. }
      generalize (classic (z = f⁻¹[y])); intros; destruct H7.
      * rewrite H7 in *; AssE [x,f[x]]; clear H6 H7.
        apply ord_set in H8; destruct H8.
        exists f[x]; unfold Restriction; apply bel_inter.
        split; SplitEnsP; split; try apply bel_universe_set; auto.
      * assert (z ∈ dom(f)). { rewrite H2; apply bel_union; tauto. }
        apply Property_Value in H8; auto; AssE [z,f[z]].
        apply ord_set in H9; destruct H9; exists f[z].
        unfold Restriction; apply bel_inter; split; SplitEnsP.
        { left; unfold Difference; apply bel_inter; split; auto.
          unfold Complement; apply Axiom_Scheme; split; Ens.
          intro; apply bel_union in H11; destruct H11.
          - apply Axiom_Scheme in H11; destruct H11; clear H11.
            assert ([x,f[x]] ∈ μ). { apply bel_universe_set; Ens. }
            apply H12 in H11; clear H12; apply ord_eq in H11; auto.
            destruct H11; rewrite H11 in H5; generalize (notin_fix x); auto.
          - apply Axiom_Scheme in H11; destruct H11; clear H11.
            assert ([(f⁻¹)[y],y] ∈ μ).
            { apply bel_universe_set; Ens; exists f.
              assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply bel_union; right.
                apply Axiom_Scheme; split; Ens. }
              rewrite dom_ran_inv' in H11; apply Property_Value in H11; auto.
              apply Axiom_SchemeP in H11; apply H11. }
            apply H12 in H11; clear H12; apply ord_eq in H11; auto.
            destruct H11; contradiction. }
        { split; try apply bel_universe_set; auto. }
  - apply Axiom_Extent; split; intros.
    + unfold Range in H5; apply Axiom_Scheme in H5; destruct H5, H6.
      unfold Restriction in H6; apply bel_inter in H6; destruct H6.
      unfold Cartesian in H7; apply Axiom_SchemeP in H7; destruct H7.
      clear H7; destruct H8; clear H8; unfold En_g' in H6.
      apply Axiom_SchemeP in H6; destruct H6, H8 as [H8|[H8|H8]].
      * unfold Difference in H8; apply bel_inter in H8; destruct H8.
        unfold Complement in H9; apply Axiom_Scheme in H9; clear H6.
        destruct H9; double H8; apply Property_ran in H10; rewrite H3 in H10.
        unfold PlusOne in H10; apply bel_union in H10; destruct H10; auto.
        apply Axiom_Scheme in H10; clear H5; destruct H10.
        rewrite H10 in *; try apply bel_universe_set; Ens; clear H10.
        double H8; apply Property_ran in H10; rewrite dom_ran_inv' in H10.
        apply Property_Value in H10; auto; apply ord_set in H6.
        destruct H6; clear H11; add ([y,x0] ∈ f⁻¹) H10; try SplitEnsP.
        apply H4 in H10; rewrite H10 in H9; elim H9.
        apply bel_union; right; SplitEns.
      * apply ord_set in H6; apply ord_eq in H8; auto; destruct H8.
        assert (x ∈ dom(f)).
        { rewrite H2; unfold PlusOne; apply bel_union; right.
          unfold Singleton; apply Axiom_Scheme; split; Ens. }
        double H10; apply Property_Value in H11; auto.
        apply Property_ran in H11; rewrite H3 in H11; unfold PlusOne in H11.
        apply bel_union in H11; rewrite H9 in *; destruct H11; auto.
        apply Axiom_Scheme in H11; clear H5; destruct H11.
        rewrite <- H11 in H8; try apply bel_universe_set; Ens.
        pattern f at 2 in H8; rewrite <- rel_inv_fix in H8; try apply H1.
        rewrite <- dom_ran_inv''' in H8; try rewrite rel_inv_fix; try apply H1; auto.
        { rewrite H8 in H7; generalize (notin_fix x); contradiction. }
        { rewrite <- dom_ran_inv; auto. }
      * apply ord_set in H6; apply ord_eq in H8; auto; destruct H8.
        rewrite H8 in H7; generalize (notin_fix x); contradiction.
    + unfold Range; apply Axiom_Scheme; split; Ens.
      assert (z∈ran(f)). { rewrite H3; unfold PlusOne; apply bel_union; auto. }
      generalize (classic (z = f[x])); intros; destruct H7.
      * rewrite H7 in *; clear H7.
        assert (y ∈ ran(f)).
        { rewrite H3; unfold PlusOne; apply bel_union; right.
          unfold Singleton; apply Axiom_Scheme; split; Ens. }
        double H7; rewrite dom_ran_inv' in H8; apply Property_Value in H8; auto.
        apply Property_ran in H8; rewrite <- dom_ran_inv in H8; rewrite H2 in H8.
        unfold PlusOne in H8; apply bel_union in H8; destruct H8.
        { exists (f⁻¹)[y]; unfold Restriction; apply bel_inter.
          split; SplitEnsP; split; try apply bel_universe_set; Ens. }
        { unfold Singleton in H8; apply Axiom_Scheme in H8; destruct H8.
          rewrite <- H9 in H5; try apply bel_universe_set; Ens.
          rewrite <- dom_ran_inv''' in H5; auto.
          generalize (notin_fix y); intros; contradiction. }
      * unfold Range in H6; apply Axiom_Scheme in H6; destruct H6, H8.
        exists x0; AssE [x0,z]; unfold Restriction; apply bel_inter; split.
        { unfold En_g'; apply Axiom_SchemeP; split; auto; left.
          unfold Difference; apply bel_inter; split; auto; unfold Complement.
          apply Axiom_Scheme; split; auto; intro; apply bel_union in H10.
          destruct H10; apply Axiom_Scheme in H10; destruct H10.
          - assert ([x,f[x]] ∈ μ); clear H10.
            { apply bel_universe_set; Ens; exists f; apply Property_Value; auto.
              rewrite H2; unfold PlusOne; apply bel_union; right.
              unfold Singleton; apply Axiom_Scheme; split; Ens. }
            apply H11 in H12; clear H11; apply ord_set in H9.
            apply ord_eq in H12; auto; destruct H12; tauto.
          - assert ([(f⁻¹)[y], y] ∈ μ); clear H10.
            { apply bel_universe_set; Ens; exists f. assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply bel_union; right.
                apply Axiom_Scheme; split; Ens. }
              rewrite dom_ran_inv' in H10; apply Property_Value in H10; auto.
              apply Axiom_SchemeP in H10; apply H10. }
            apply H11 in H12; clear H11; apply ord_set in H9.
            apply ord_eq in H12; auto; destruct H12; rewrite H11 in H5.
            generalize (notin_fix y); intros; contradiction. }
        { double H8; apply Property_dom in H10; rewrite H2 in H10.
          unfold PlusOne in H10; apply bel_union in H10; unfold Cartesian.
          apply Axiom_SchemeP; repeat split; auto; try apply bel_universe_set; Ens.
          destruct H10; auto; apply Axiom_Scheme in H10; destruct H10.
          rewrite H11 in H8; try apply bel_universe_set; Ens; double H8.
          apply Property_dom in H12; apply Property_Value in H12; auto.
          add ([x,z] ∈ f) H12; apply H1 in H12; symmetry in H12; tauto. }
Qed.

Hint Resolve equiv_plus_equiv : set.


(* 164 Theorem  w ⊂ C. *)

Theorem W_sub_C : W ⊂ C.
Proof.
  intros.
  unfold Subclass; apply Mathematical_Induction.
  - assert (Φ ∈ W); try apply zero_not_int; try apply W.
    unfold W in H; apply Axiom_Scheme in H; destruct H; unfold NInteger in H0.
    destruct H0; unfold C; apply Axiom_Scheme.
    unfold Cardinal_Number, Ordinal_Number; repeat split; intros; auto.
    + unfold R; apply Axiom_Scheme; split; auto.
    + unfold Less in H3; generalize (not_bel_zero y); contradiction.
  - intros; destruct H; double H; apply int_succ in H1; unfold W in H1.
    apply Axiom_Scheme in H1; unfold NInteger in H1; destruct H1, H2.
    unfold C in H0; apply Axiom_Scheme in H0; destruct H0.
    unfold Cardinal_Number, Ordinal_Number in H4; destruct H4.
    unfold C; apply Axiom_Scheme; split; auto; split; intros.
    + unfold Ordinal_Number, R; apply Axiom_Scheme; split; auto.
    + unfold Less, PlusOne in H7; apply bel_union in H7; destruct H7.
      * assert (y ∈ W).
        { unfold W; apply Axiom_Scheme; split; Ens.
          unfold W in H; apply Axiom_Scheme in H; destruct H.
          apply int_bel_int in H7; auto. }
        intro; clear H6; double H8; apply Axiom_Scheme in H6; destruct H6.
        unfold NInteger in H10; destruct H10; unfold WellOrdered in H11.
        destruct H11 as [H12 H11]; clear H12.
        generalize (classic (y = Φ)); intros; destruct H12.
        { rewrite H12 in H9; clear H12; unfold Equivalent in H9.
          destruct H9 as [f H9]; destruct H9, H12.
          assert (k ∈ (PlusOne k)).
          { unfold PlusOne; apply bel_union; right; unfold Singleton.
            apply Axiom_Scheme; split; Ens. }
          rewrite <- H12 in H14; unfold Function1_1 in H9; destruct H9.
          apply Property_Value in H14; auto; apply Property_ran in H14.
          rewrite H13 in H14; generalize (not_bel_zero f[k]); contradiction. }
        { assert (y ⊂ y /\ y ≠ Φ). { split; unfold Subclass; Ens. }
          apply H11 in H13; clear H11 H12; destruct H13.
          assert (y = PlusOne x).
          { apply ordnum_plus_eq; split; auto; try apply Axiom_Scheme; Ens. }
          unfold FirstMember in H11; destruct H11; clear H13.
          rewrite H12 in H9; apply equiv_plus_equiv in H9; auto.
          - assert (x ∈ R /\ x ≺ k).
            { unfold Less; split.
              - unfold R; apply Axiom_Scheme; split; Ens.
                apply ord_bel_ord with (x:= y); auto.
              - unfold R in H4; apply Axiom_Scheme in H4; destruct H4.
                unfold Ordinal, full in H13; destruct H13.
                apply H14 in H7; apply H7 in H11; auto. }
            destruct H13; apply H5 in H14; auto.
          - generalize Property_W; intros; unfold Ordinal, full in H13.
            destruct H13; apply H14 in H8; apply H8 in H11; auto. }
      * unfold Singleton in H7; apply Axiom_Scheme in H7; destruct H7.
        assert (k ∈ μ); try apply bel_universe_set; Ens; apply H8 in H9.
        clear H6 H7 H8; rewrite H9; intro; clear H9; double H.
        apply Axiom_Scheme in H7; clear H0; destruct H7; unfold NInteger in H7.
        destruct H7; unfold WellOrdered in H8; destruct H8; clear H8.
        generalize (classic (k = Φ)); intros; destruct H8.
        { rewrite H8 in H6; clear H8; unfold Equivalent in H6.
          destruct H6 as [f H6]; destruct H6, H8.
          assert (Φ ∈ (PlusOne Φ)).
          { unfold PlusOne; apply bel_union; right; unfold Singleton.
            apply Axiom_Scheme; split; auto; generalize Axiom_Infinity; intros.
            destruct H11, H11, H12; Ens. }
          rewrite <- H8 in H11; unfold Function1_1 in H6; destruct H6.
          apply Property_Value in H11; auto; apply Property_ran in H11.
          rewrite H10 in H11; generalize (not_bel_zero f[Φ]); contradiction. }
        { assert (k ⊂ k /\ k ≠ Φ). { split; unfold Subclass; Ens. }
          apply H9 in H10; clear H8 H9; destruct H10.
          assert (k = PlusOne x).
          { apply ordnum_plus_eq; split; auto; try apply Axiom_Scheme; Ens. }
          unfold FirstMember in H8; destruct H8; clear H10.
          pattern k at 2 in H6; rewrite H9 in H6; apply equiv_plus_equiv in H6; auto.
          - apply H5 in H8; try contradiction; unfold R; apply Axiom_Scheme.
            split; Ens; apply ord_bel_ord with (x:= k); auto.
          - unfold W; apply Axiom_Scheme; split; Ens.
            apply Axiom_Scheme in H; destruct H; apply int_bel_int in H8; auto. }
Qed.

Hint Resolve W_sub_C : set.


(* 165 Theorem  W ∈ C. *)

Theorem W_bel_C : W ∈ C.
Proof.
  generalize W_bel_R; intros; AssE W.
  unfold C; apply Axiom_Scheme; split; auto.
  unfold Cardinal_Number; split; intros.
  - unfold Ordinal_Number; auto.
  - unfold Less in H2; intro; double H2.
    apply int_succ in H4.
    assert (Ensemble (PlusOne y) /\ y ⊂ (PlusOne y)).
    { split; Ens; unfold PlusOne, Subclass; intros.
      apply bel_union; tauto. }
    apply card_le in H5.
    assert (Ensemble W /\ (PlusOne y) ⊂ W).
    { split; auto; unfold PlusOne, Subclass; intros.
      apply bel_union in H6; destruct H6.
      - unfold W in H2; apply Axiom_Scheme in H2; destruct H2.
        unfold W; apply Axiom_Scheme; split; Ens.
        apply int_bel_int in H6; auto.
      - unfold Singleton in H6; apply Axiom_Scheme in H6; destruct H6.
        rewrite H7; try apply bel_universe_set; Ens. }
    apply card_le in H6; apply card_eq in H3; Ens.
    unfold LessEqual in H5, H6; destruct H5, H6.
    + generalize (not_bel_and P[y] P[PlusOne y]); intros.
      rewrite H3 in H6; elim H7; split; auto.
    + rewrite H3 in H6; rewrite <- H6 in H5.
      generalize (notin_fix P[PlusOne y]); intros; contradiction.
    + rewrite H3, H5 in H6.
      generalize (notin_fix P[PlusOne y]); intros; contradiction.
    + apply card_eq in H5; Ens.
      apply W_sub_C in H4; unfold C in H4.
      apply Axiom_Scheme in H4; destruct H4; unfold Cardinal_Number in H7.
      destruct H7; apply H8 in H1.
      * elim H1; apply equiv_com; auto.
      * unfold Less, PlusOne; apply bel_union; right.
        unfold Singleton; apply Axiom_Scheme; Ens.
Qed.

Hint Resolve W_bel_C : set.


(* 166 Definition  x is finite if and only if P(x)∈W. *)

Definition Finite (x: Class) : Prop := P [x] ∈ W.

Corollary Property_Finite : forall x, Finite x -> Ensemble x.
Proof.
  intros; unfold Finite in H.
  generalize (classic (Ensemble x)); intros; destruct H0; auto.
  generalize card_fun; intros; destruct H1, H2.
  assert (x ∉ dom(P)).
  { rewrite H2; intro; apply bel_universe_set in H4; contradiction. }
  apply dom_value in H4; rewrite H4 in H; AssE μ.
  generalize universe_notset; intros; contradiction.
Qed.

Hint Unfold Finite : set.


(* 167 Theorem  x is finite if and only if there is r such that r well-orders x
   and r⁻¹ well-orders x. *)

Lemma lem_fin_iff_well : forall r x f,
  WellOrdered r P[x] -> Function1_1 f -> dom(f) = x ->
  ran(f) = P[x] -> WellOrdered \{\ λ u v, Rrelation f[u] r f[v] \}\ x.
Proof.
  intros.
  unfold Function1_1 in H0; destruct H0.
  unfold WellOrdered; split; intros.
  - unfold Connect; intros; destruct H4; rewrite <- H1 in H4, H5.
    AssE u; AssE v; apply Property_Value in H4; auto.
    apply Property_Value in H5; auto; double H4; double H5.
    apply Property_ran in H8; apply Property_ran in H9.
    rewrite H2 in H8, H9; unfold WellOrdered, Connect in H.
    destruct H; clear H10; add (f[v] ∈ P[x]) H8; apply H in H8.
    clear H H9; destruct H8 as [H | [H | H]].
    + left; unfold Rrelation; apply Axiom_SchemeP;split;try apply ord_set;Ens.
    + right; left; apply Axiom_SchemeP; split; try apply ord_set; auto.
    + right; right; rewrite H in H4; clear H.
      assert ([f[v],u] ∈ f⁻¹ /\ [f[v],v] ∈ f⁻¹).
      { unfold Inverse; split; apply Axiom_SchemeP; split; auto.
        - apply ord_set; split; apply Property_ran in H4; Ens.
        - apply ord_set; split; apply Property_ran in H5; Ens. }
      unfold Function in H3; apply H3 in H; auto.
  - assert (ran(f|(y)) ⊂ P [x] /\ ran(f|(y)) ≠ Φ).
    { destruct H4; split.
      - unfold Subclass; intros; unfold Range in H6; apply Axiom_Scheme in H6.
        destruct H6, H7; unfold Restriction in H7; apply bel_inter in H7.
        destruct H7; apply Property_ran in H7; rewrite H2 in H7; auto.
      - apply not_zero_exist_bel in H5; destruct H5; double H5; apply H4 in H6.
        rewrite <- H1 in H6; apply Property_Value in H6; auto.
        double H6; apply Property_ran in H7; apply not_zero_exist_bel.
        exists f[x0]; unfold Range; apply Axiom_Scheme; split; Ens.
        exists x0; unfold Restriction; apply bel_inter; split; auto.
        unfold Cartesian; apply Axiom_SchemeP; repeat split; Ens.
        apply bel_universe_set; Ens. }
    apply H in H5; unfold FirstMember in H5; destruct H5, H5.
    unfold Range in H5; apply Axiom_Scheme in H5; destruct H5, H7.
    unfold Restriction in H7; apply bel_inter in H7; destruct H7.
    exists x1; unfold FirstMember; split; intros.
    + unfold Cartesian in H8; apply Axiom_SchemeP in H8; apply H8.
    + clear H8; double H9; apply H4 in H9; rewrite <- H1 in H9.
      apply Property_Value in H9; auto.
      assert (f[y0] ∈ ran(f|(y))).
      { AssE [y0,f[y0]]; apply ord_set in H10; destruct H10.
        unfold Range; apply Axiom_Scheme; split; auto.
        exists y0; unfold Restriction; apply bel_inter; split; auto.
        apply Axiom_SchemeP; repeat split; try apply ord_set; auto.
        apply bel_universe_set; auto. }
      apply H6 in H10; clear H6; intro; elim H10; clear H10.
      unfold Rrelation at 1 in H6; apply Axiom_SchemeP in H6; destruct H6.
      double H7; apply Property_dom in H11; apply Property_Value in H11; Ens.
      add ([x1,f[x1]] ∈ f) H7; apply H0 in H7; rewrite H7; auto.
Qed.

Theorem fin_iff_well : forall x,
  Finite x <-> exists r, WellOrdered r x /\ WellOrdered (r⁻¹) x.
Proof.
  intros; split; intros.
  - double H; unfold Finite in H; apply Property_Finite in H0.
    unfold W in H; apply Axiom_Scheme in H; destruct H.
    unfold NInteger in H1; destruct H1; apply ord_well_order in H1.
    apply card_equiv in H0; apply equiv_com in H0.
    unfold Equivalent in H0; destruct H0 as [f H0], H0, H3.
    exists (\{\ λ u v, Rrelation f[u] E f[v] \}\); split.
    + apply lem_fin_iff_well; auto.
    + assert (\{\ λ u v, Rrelation f [u] E f [v] \}\⁻¹ =
              \{\ λ u v, Rrelation f [u] E⁻¹ f [v] \}\).
      { apply Axiom_Extent; split; intros.
        - PP H5 a b; apply Axiom_SchemeP.
          apply Axiom_SchemeP in H6; destruct H6.
          apply Axiom_SchemeP in H7; destruct H7; split; auto.
          unfold Rrelation in H8; unfold Rrelation, Inverse.
          apply Axiom_SchemeP; split; auto; AssE [f[b],f[a]].
          apply ord_set in H9; destruct H9; apply ord_set; auto.
        - PP H5 a b; apply Axiom_SchemeP in H6; destruct H6.
          unfold Rrelation, Inverse in H7.
          apply Axiom_SchemeP in H7; destruct H7.
          apply ord_set in H6; destruct H6; apply Axiom_SchemeP.
          split; try apply ord_set; auto; apply Axiom_SchemeP.
          split; try apply ord_set; auto. }
      rewrite H5; apply lem_fin_iff_well; auto.
  - destruct H as [r H], H; unfold Finite.
    generalize ord_not_set_R; intros; destruct H1; clear H2.
    apply ord_well_order in H1; add (WellOrdered E R) H; clear H1.
    apply well_order_pre in H; destruct H as [f H], H, H1.
    unfold Order_PXY in H1; destruct H1, H3, H4, H5; double H6.
    apply sec_R_ord in H7; add (Ordinal W) H7; try apply Property_W.
    apply ord_bel_eq in H7; destruct H7.
    + destruct H2.
      * assert (P[x] = ran(f)).
        { apply W_sub_C in H7; clear H0; AssE ran(f).
          apply order_pre_fun1_inv in H4; destruct H4; clear H8.
          assert (dom(f) ≈ ran(f)). { unfold Equivalent; exists f; auto. }
          unfold Function1_1 in H4; destruct H4.
          rewrite (dom_ran_inv f), (dom_ran_inv' f) in *.
          apply Axiom_Substitution in H0; auto; rewrite H2 in *; double H0.
          apply card_equiv in H0; apply Property_PClass in H10.
          apply equiv_tran with (z:= dom(f⁻¹)) in H0; auto; clear H2 H8.
          unfold C in H7, H10; apply Axiom_Scheme in H7.
          apply Axiom_Scheme in H10.
          destruct H7, H10; clear H2 H8; destruct H7, H10.
          unfold Ordinal_Number in H2, H8; double H2; double H8.
          unfold R in H11, H12; apply Axiom_Scheme in H11.
          apply Axiom_Scheme in H12.
          destruct H11, H12; add (Ordinal dom(f⁻¹)) H14; clear H11 H12 H13.
          apply ord_bel_eq in H14; destruct H14 as [H11 | [H11 | H11]]; auto.
          - apply H7 in H11; auto; apply equiv_com in H0; contradiction.
          - apply H10 in H11; auto; contradiction. }
          rewrite H8; auto.
      * rewrite H2 in H7; add (W ∈ R) H7; try apply W_bel_R.
        generalize (not_bel_and R W); intros; contradiction.
    + assert (W ⊂ ran(f)).
      { destruct H7; try (rewrite H7; unfold Subclass; auto).
        apply sec_R_ord in H6; unfold Ordinal, full in H6.
        destruct H6; apply H8 in H7; auto. }
      assert (~ exists z, FirstMember z E⁻¹ W).
      { intro; destruct H9; unfold FirstMember in H9; destruct H9.
        AssE x0; apply int_succ in H9; AssE (PlusOne x0).
        apply H10 in H9; elim H9; clear H9 H10.
        unfold Rrelation, Inverse, E; apply Axiom_SchemeP.
        split; try apply ord_set; auto; apply Axiom_SchemeP.
        split; try apply ord_set; auto; unfold PlusOne.
        apply bel_union; right; apply Axiom_Scheme; auto. }
      double H5; unfold Section in H10; destruct H10; clear H11.
      apply lem_order_pre_sec_sub with (r:= r⁻¹) in H10; auto; clear H6; double H4.
      apply order_pre_fun1_inv in H6; destruct H6; clear H11; destruct H6 as [H11 H6].
      clear H11; elim H9; clear H9; unfold WellOrdered in H10; destruct H10.
      assert (ran(f⁻¹|(W)) ⊂ dom(f) /\ ran(f⁻¹|(W)) ≠ Φ).
      { split; unfold Subclass; intros.
        - unfold Range in H11; apply Axiom_Scheme in H11; destruct H11, H12.
          unfold Restriction in H12; apply bel_inter in H12; destruct H12.
          unfold Inverse in H12; apply Axiom_SchemeP in H12; destruct H12.
          apply Property_dom in H14; auto.
        - assert (Φ ∈ W); try apply zero_not_int; auto; double H11.
          apply H8 in H12; rewrite dom_ran_inv' in H12.
          apply Property_Value in H12; auto; AssE [Φ,(f⁻¹)[Φ]].
          apply ord_set in H13; destruct H13; apply not_zero_exist_bel.
          exists f⁻¹[Φ]; unfold Range; apply Axiom_Scheme; split; auto.
          exists Φ; unfold Restriction; apply bel_inter; split; auto.
          apply Axiom_SchemeP; repeat split; try apply ord_set; auto.
          apply bel_universe_set; auto. }
      apply H10 in H11; clear H10; destruct H11; exists f[x0].
      unfold FirstMember in H10; destruct H10.
      unfold FirstMember; split; intros.
      * clear H11; apply Axiom_Scheme in H10; destruct H10, H11.
        unfold Restriction in H11; apply bel_inter in H11; destruct H11.
        apply Axiom_SchemeP in H12; destruct H12 as [_ H12], H12 as [H12 _].
        unfold Inverse in H11; apply Axiom_SchemeP in H11.
        destruct H11; double H13.
        apply Property_dom in H14; apply Property_Value in H14; auto.
        add ([x0,f[x0]] ∈ f) H13; clear H14; unfold Function in H.
        apply H in H13; rewrite H13 in H12; auto.
      * double H12; apply H8 in H13; apply Axiom_Scheme in H13.
        destruct H13, H14.
        AssE [x1,y]; apply ord_set in H15; destruct H15; clear H16.
        assert (x1 ∈ ran(f⁻¹|(W))).
        { unfold Range; apply Axiom_Scheme; split; auto; exists y.
          unfold Restriction; apply bel_inter; split.
          - unfold Inverse; apply Axiom_SchemeP.
            split; try apply ord_set; auto.
          - unfold Cartesian; apply Axiom_SchemeP.
            repeat split; try apply ord_set; auto; apply bel_universe_set; auto. }
        apply H11 in H16; clear H11; unfold Range in H10.
        apply Axiom_Scheme in H10.
        destruct H10, H11; unfold Restriction in H11; apply bel_inter in H11.
        destruct H11; clear H17; unfold Inverse in H11.
        apply Axiom_SchemeP in H11.
        clear H10; destruct H11; apply Property_dom in H11; double H14.
        apply Property_dom in H17; add (x1 ∈ dom(f)) H11; double H11; clear H17.
        unfold Connect in H9; apply H9 in H18; clear H9; intro.
        unfold Rrelation, Inverse, E in H9; apply Axiom_SchemeP in H9.
        destruct H9; clear H9; apply Axiom_SchemeP in H17; destruct H17.
        destruct H18 as [H18|[H18|H18]]; try contradiction.
        { clear H16; unfold Order_Pr in H4; destruct H11.
          assert (x1 ∈ dom(f) /\ x0 ∈ dom(f) /\ Rrelation x1 r x0).
          { repeat split; auto; unfold Rrelation, Inverse in H18.
            apply Axiom_SchemeP in H18; unfold Rrelation; apply H18. }
          apply H4 in H19; clear H4 H9 H13 H15; unfold Rrelation, E in H19.
          apply Axiom_SchemeP in H19; destruct H19; clear H4.
          apply Property_Value in H16; auto; add ([x1,f[x1]] ∈ f) H14.
          apply H in H14; rewrite H14 in H17; add (f[x1] ∈ f[x0]) H17.
          generalize (not_bel_and f[x0] f[x1]); intros; contradiction. }
        { rewrite H18 in H17; clear H9 H15 H16; destruct H11.
          apply Property_Value in H11; auto; add ([x1,y] ∈ f) H11.
          unfold Function in H; apply H in H11; rewrite H11 in H17.
          generalize (notin_fix y); intros; contradiction. }
Qed.

Hint Resolve fin_iff_well : set.


(* Some properties about finite *)

Lemma Finite_Subclass : forall (A B: Class),
  Finite A -> B ⊂ A -> Finite B.
Proof.
  intros.
  apply fin_iff_well in H; destruct H as [r H], H.
  apply fin_iff_well; exists r; split.
  - unfold WellOrdered, Connect in H; destruct H.
    unfold WellOrdered, Connect; split; intros.
    + destruct H3; apply H; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply sub_tran in H3; auto.
  - unfold WellOrdered, Connect in H1; destruct H1.
    unfold WellOrdered, Connect; split; intros.
    + destruct H3; apply H1; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply sub_tran in H3; auto.
Qed.


Lemma Finite_Single : forall z, Ensemble z -> Finite ([z]).
Proof.
  intros.
  apply fin_iff_well; exists E; split.
  - unfold WellOrdered; split; intros.
    + unfold Connect; intros; destruct H0; unfold Singleton in H0, H1.
      apply Axiom_Scheme in H0; apply Axiom_Scheme in H1.
      destruct H0, H1; double H.
      apply bel_universe_set in H; apply bel_universe_set in H4; apply H2 in H.
      apply H3 in H4; rewrite <- H4 in H; tauto.
    + destruct H0; apply not_zero_exist_bel in H1; destruct H1; exists x.
      unfold FirstMember; split; auto; intros; unfold Subclass in H0.
      apply H0 in H1; apply H0 in H2; unfold Singleton in H1, H2; double H.
      apply Axiom_Scheme in H1; apply Axiom_Scheme in H2; destruct H1, H2.
      apply bel_universe_set in H; apply bel_universe_set in H3; apply H4 in H.
      apply H5 in H3; rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation in H6; unfold E in H6; apply Axiom_SchemeP in H6.
      destruct H6; generalize (notin_fix y0); intros; contradiction.
  - unfold WellOrdered; split; intros.
    + unfold Connect; intros; destruct H0; unfold Singleton in H0, H1.
      apply Axiom_Scheme in H0; apply Axiom_Scheme in H1; destruct H0, H1.
      double H; apply bel_universe_set in H; apply bel_universe_set in H4.
      apply H2 in H; apply H3 in H4; rewrite <- H4 in H; tauto.
    + destruct H0; apply not_zero_exist_bel in H1; auto; destruct H1; exists x.
      unfold FirstMember; split; auto; intros; unfold Subclass in H0.
      apply H0 in H1; apply H0 in H2; unfold Singleton in H1, H2; double H.
      apply Axiom_Scheme in H1; apply Axiom_Scheme in H2; destruct H1, H2.
      apply bel_universe_set in H; apply bel_universe_set in H3; apply H4 in H.
      apply H5 in H3; rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation, Inverse in H6; apply Axiom_SchemeP in H6.
      destruct H6; unfold E in H7; apply Axiom_SchemeP in H7.
      destruct H7; generalize (notin_fix y0); intros; contradiction.
Qed.


(* 168 Theorem  If x and y are finite so is x∪y. *)

Theorem fin_union : forall x y,
  Finite x /\ Finite y -> Finite (x ∪ y).
Proof.
  intros; destruct H.
  apply fin_iff_well in H; apply fin_iff_well in H0.
  destruct H as [r H], H0 as [s H0], H, H0; apply fin_iff_well.
  exists (\{\ λ u v, (u∈x /\ v∈x /\ Rrelation u r v) \/ (u∈(y~x) /\
  v∈(y~x) /\ Rrelation u s v) \/ (u∈x /\ v∈(y~x)) \}\); split.
  - clear H1 H2; unfold WellOrdered in H, H0; destruct H, H0.
    unfold WellOrdered; split; intros.
    + clear H1 H2; unfold Connect in H, H0; unfold Connect; intros.
      destruct H1; apply bel_union in H1; apply bel_union in H2.
      unfold Rrelation; destruct H1, H2.
      * clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
        clear H; destruct H0 as [H | [H | H]]; try tauto.
        { left; SplitEnsP. } { right; left; SplitEnsP. }
      * clear H0; generalize (classic (v ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { left; SplitEnsP; right; right; split; auto; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
      * clear H0; generalize (classic (u ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { right; left; SplitEnsP.
          right; right; split; auto; unfold Difference; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
      * generalize (classic (u∈x)) (classic (v∈x)); intros; destruct H3, H4.
        { clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
          clear H; destruct H0 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { left; SplitEnsP; right; right; split; auto; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
        { right; left; SplitEnsP; right; right; split; auto; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
        { clear H; assert (u ∈ y /\ v ∈ y); auto; apply H0 in H.
          clear H0; destruct H as [H | [H | H]]; try tauto.
          - left; SplitEnsP; right; left; repeat split; auto.
            + apply bel_inter; split; auto; SplitEns.
            + apply bel_inter; split; auto; SplitEns.
          - right; left; SplitEnsP.
            right; left; unfold Difference; repeat split; auto.
            + apply bel_inter; split; auto; SplitEns.
            + apply bel_inter; split; auto; SplitEns. }
    + generalize (classic (\{ λ z, z ∈ y0 /\ z ∈ x \} = Φ)).
      clear H H0; destruct H3; intros; destruct H3.
      * assert (y0 ⊂ y).
        { unfold Subclass; intros; double H4.
          apply H in H5; apply bel_union in H5; destruct H5; auto.
          generalize (not_bel_zero z); intros; elim H6; clear H6.
          rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
        add (y0 ≠ Φ) H4; apply H2 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply Axiom_SchemeP in H1; destruct H1.
        unfold Rrelation; destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (not_bel_zero y1); intros.
          elim H5; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
        { destruct H4; clear H5; generalize (not_bel_zero y1); intros.
          elim H5; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈x\} ⊂ x).
        { unfold Subclass; intros; apply Axiom_Scheme in H4; apply H4. }
        add (\{λ z, z∈y0 /\ z∈x\} <> Φ) H4; apply H1 in H4; clear H1 H2.
        destruct H4 as [z H1]; exists z; unfold FirstMember in H1.
        destruct H1; apply Axiom_Scheme in H1; destruct H1, H4.
        unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H7.
        { assert (y1 ∈ \{λ z, z∈y0 /\ z∈x\}).
          { apply Axiom_Scheme; repeat split; Ens. }
          apply H2 in H8; intro; elim H8; clear H2 H8.
          unfold Rrelation in H9; apply Axiom_SchemeP in H9; destruct H9.
          unfold Rrelation; destruct H8 as [H8|[H8|H8]]; try apply H8.
          - destruct H8; clear H9; unfold Difference in H8.
            apply Axiom_Scheme in H8; destruct H8, H9; unfold Complement in H10.
            apply Axiom_Scheme in H10; destruct H10; contradiction.
          - destruct H8; clear H8; unfold Difference in H9.
            apply Axiom_Scheme in H9; destruct H9, H9; unfold Complement in H10.
            apply Axiom_Scheme in H10; destruct H10; contradiction. }
        { intro; unfold Rrelation in H8; apply Axiom_SchemeP in H8.
          destruct H8, H9 as [H9|[H9|H9]], H9; try contradiction.
          destruct H10; clear H8 H9 H11; unfold Difference in H10.
          apply Axiom_Scheme in H10; destruct H10, H9; unfold Complement in H10.
          apply Axiom_Scheme in H10; destruct H10; contradiction. }
  - unfold WellOrdered; split; intros.
    + clear H1 H2; unfold WellOrdered in H, H0; destruct H, H0.
      clear H1 H2; unfold Connect in H, H0; unfold Connect; intros.
      destruct H1; apply bel_union in H1; apply bel_union in H2.
      unfold Rrelation; destruct H1, H2.
      * clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
        clear H; destruct H0 as [H | [H | H]]; try tauto.
        { right; left; unfold Inverse; SplitEnsP; SplitEnsP. }
        { left; SplitEnsP; SplitEnsP. }
      * clear H0; generalize (classic (v ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { right; left; SplitEnsP; SplitEnsP.
          right; right; split; auto; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
      * clear H0; generalize (classic (u ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { left; SplitEnsP; SplitEnsP.
          right; right; split; auto; unfold Difference; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
      * generalize (classic (u∈x)) (classic (v∈x)); intros; destruct H3, H4.
        { clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
          clear H; destruct H0 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { right; left; SplitEnsP; SplitEnsP.
          right; right; split; auto; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
        { left; SplitEnsP; SplitEnsP.
          right; right; split; auto; unfold Difference; apply bel_inter.
          split; auto; unfold Complement; SplitEns. }
        { clear H; assert (u ∈ y /\ v ∈ y); auto; apply H0 in H.
          clear H0; destruct H as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
            right; left; unfold Difference; repeat split; auto.
            + apply bel_inter; split; auto; SplitEns.
            + apply bel_inter; split; auto; SplitEns.
          - left; SplitEnsP; SplitEnsP; right; left; repeat split; auto.
            + apply bel_inter; split; auto; SplitEns.
            + apply bel_inter; split; auto; SplitEns. }
    + clear H H0; unfold WellOrdered in H1, H2.
      destruct H1, H2; clear H H1; destruct H3.
      generalize (classic (\{λ z, z∈y0 /\ z∈(y~x)\}=Φ)); intros; destruct H3.
      * assert (y0 ⊂ x).
        { unfold Subclass; intros; double H4.
          apply H in H5; apply bel_union in H5; destruct H5; auto.
          generalize (classic (z ∈ x)); intros; destruct H6; auto.
          generalize (not_bel_zero z); intros; elim H7; clear H7.
          rewrite <- H3; apply Axiom_Scheme; repeat split; Ens.
          unfold Difference; apply bel_inter; split; auto.
          unfold Complement; apply Axiom_Scheme; split; Ens. }
        add (y0 ≠ Φ) H4; apply H0 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply Axiom_SchemeP in H1; destruct H1.
        apply Axiom_SchemeP in H4; destruct H4 as [H5 H4]; clear H5.
        unfold Rrelation, Inverse; apply Axiom_SchemeP; split; auto.
        destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (not_bel_zero z); intros.
          elim H5; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
        { destruct H4; clear H4; generalize (not_bel_zero y1); intros.
          elim H4; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈(y~x)\} ⊂ y).
        { unfold Subclass; intros; apply Axiom_Scheme in H4; destruct H4, H5.
          unfold Difference in H6; apply bel_inter in H6; apply H6. }
        add (\{λ z, z∈y0 /\ z∈(y~x)\} <> Φ) H4; apply H2 in H4; clear H0 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; apply Axiom_Scheme in H0; destruct H0, H4.
        unfold Difference in H5; apply bel_inter in H5; destruct H5.
        unfold Complement in H6; apply Axiom_Scheme in H6; clear H0.
        destruct H6; unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H8.
        { intro; unfold Rrelation in H9; apply Axiom_SchemeP in H9; destruct H9.
          apply Axiom_SchemeP in H10; destruct H10 as [H11 H10]; clear H11.
          destruct H10 as [H10|[H10|H10]], H10; try contradiction.
          destruct H11; clear H9 H10 H12; unfold Difference in H11.
          apply Axiom_Scheme in H11; destruct H11, H10;unfold Complement in H11.
          apply Axiom_Scheme in H11; destruct H11; contradiction. }
        { assert (y1 ∈ \{λ z, z ∈ y0 /\ z ∈ (y ~ x)\}).
          { apply Axiom_Scheme; repeat split; Ens; apply H in H7.
            apply bel_union in H7; destruct H7; try contradiction.
            apply bel_inter; split; auto; apply Axiom_Scheme; split; Ens. }
          apply H2 in H9; intro; elim H9; clear H2 H9.
          unfold Rrelation in H10; apply Axiom_SchemeP in H10; destruct H10.
          apply Axiom_SchemeP in H9; destruct H9 as [H10 H9]; clear H10.
          unfold Rrelation, Inverse; SplitEnsP.
          destruct H9 as [H9|[H9|H9]], H9; try contradiction; apply H10. }
Qed.

Hint Resolve fin_union : set.


(* 169 Theorem  If x is finite and each member of x is finite, then ∪x is
   finite. *)

Lemma mem_fix_bel_sing : forall x y, x ∈ y -> y = (y ~ [x] ∪ [x]).
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - generalize (classic (z ∈ [x])); intros; destruct H1.
    + apply bel_union; right; auto.
    + apply bel_union; left; unfold Difference; apply bel_inter.
      split; auto; unfold Complement; apply Axiom_Scheme; Ens.
  - apply bel_union in H0; destruct H0.
    + unfold Difference in H0; apply bel_inter in H0; apply H0.
    + unfold Singleton in H0; apply Axiom_Scheme in H0; destruct H0.
      rewrite H1; try apply bel_universe_set; Ens.
Qed.

Lemma eleU_union : forall x y, ∪(x ∪ y) = (∪x) ∪ (∪y).
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H, H0, H0.
    apply bel_union in H1; destruct H1.
    + apply bel_union; left; apply Axiom_Scheme; Ens.
    + apply bel_union; right; apply Axiom_Scheme; Ens.
  - apply bel_union in H; destruct H.
    + apply Axiom_Scheme in H; destruct H, H0, H0.
      apply Axiom_Scheme; split; Ens; exists x0.
      split; auto; apply bel_union; auto.
    + apply Axiom_Scheme in H; destruct H, H0, H0.
      apply Axiom_Scheme; split; auto; exists x0.
      split; auto; apply bel_union; auto.
Qed.

Theorem fin_eleU : forall (x: Class),
  Finite x -> (forall z, z∈x -> Finite z) -> Finite (∪ x).
Proof.
  intros; double H.
  unfold Finite in H; apply Property_Finite in H1.
  assert (\{λ u, u∈W /\ (forall y, P[y] = u /\ Ensemble y /\
            (forall z, z∈y -> Finite z) -> Finite (∪ y)) \} = W).
  { apply math_ind.
    - unfold Subclass; intros; apply Axiom_Scheme in H2; apply H2.
    - apply Axiom_Scheme; generalize (zero_not_int x); intros; destruct H2.
      clear H3; repeat split; Ens; intros; destruct H3, H4.
      generalize (classic (y = Φ)); intros; destruct H6.
      + rewrite H6 in *; rewrite zero_eleU_zero; unfold Finite; rewrite H3; auto.
      + apply not_zero_exist_bel in H6; destruct H6; apply card_equiv in H1.
        apply card_equiv in H4; apply equiv_com in H4; unfold Equivalent in H4.
        destruct H4 as [f H4], H4, H4, H7; rewrite <- H7 in H6.
        apply Property_Value in H6; auto; apply Property_ran in H6.
        rewrite H9, H3 in H6; generalize (not_bel_zero f[x0]); contradiction.
    - intros; apply Axiom_Scheme in H2; apply Axiom_Scheme.
      destruct H2, H3; double H3.
      apply int_succ in H5; repeat split; Ens; intros; destruct H6, H7.
      AssE y; clear H7; double H9; unfold PlusOne in H6; apply card_equiv in H9.
      unfold Equivalent in H9; destruct H9 as [f H9], H9, H9, H10.
      assert (u ∈ P[y]).
      { rewrite H6; apply bel_union; right; unfold Singleton.
        apply Axiom_Scheme; split; Ens. }
      rewrite <- H10 in H13; apply Property_Value in H13; auto.
      apply Property_ran in H13; rewrite H12 in H13.
      apply mem_fix_bel_sing in H13; rewrite H13; clear H13.
      rewrite eleU_union; apply fin_union; split.
      + apply H4; assert (Ensemble (y ~ [f[u]])).
        { apply (sub_set y _); auto; unfold Subclass; intros.
          unfold Difference in H13; apply bel_inter in H13; apply H13. }
        repeat split; auto; intros.
        * apply W_sub_C in H3; apply card_iff_eq in H3; clear H2; destruct H3.
          rewrite <- H3 at 2; add (Ensemble u) H13; apply card_eq in H13.
          apply H13; clear H13; apply equiv_com; unfold Equivalent.
          exists (f|(P[y]~[u])).
          { repeat split; unfold Relation; intros.
            - unfold Restriction in H13; apply bel_inter in H13.
              destruct H13; PP H14 a b; Ens.
            - unfold Restriction in H13; destruct H13; apply bel_inter in H13.
              apply bel_inter in H14; destruct H13, H14; unfold Function in H9.
              apply H9 with (x:= x0); split; auto.
            - PP H13 a b; Ens.
            - unfold Inverse, Restriction in H13; destruct H13.
              apply Axiom_SchemeP in H13; apply Axiom_SchemeP in H14.
              destruct H13, H14.
              apply bel_inter in H15; apply bel_inter in H16; destruct H15, H16.
              clear H17 H18; unfold Function in H11; apply H11 with (x:= x0).
              split; apply Axiom_SchemeP; Ens.
            - apply Axiom_Extent; split; intros.
              + unfold Domain in H13; apply Axiom_Scheme in H13.
                destruct H13, H14.
                unfold Restriction in H14; apply bel_inter in H14; destruct H14.
                clear H14; unfold Cartesian in H15; apply Axiom_SchemeP in H15.
                destruct H15, H15; clear H16; unfold Difference in H15.
                apply bel_inter in H15; destruct H15; rewrite H6 in H15.
                apply bel_union in H15; destruct H15; auto.
                unfold Complement in H16; apply Axiom_Scheme in H16.
                destruct H16; contradiction.
              + unfold Domain; apply Axiom_Scheme; split; Ens; exists f[z].
                unfold Restriction; apply bel_inter.
                assert (z ∈ dom(f)). { rewrite H10, H6; apply bel_union; tauto. }
                apply Property_Value in H14; auto; split; auto.
                unfold Cartesian; apply Axiom_SchemeP; split; Ens; double H14.
                apply Property_ran in H15; split; try apply bel_universe_set; Ens.
                clear H15; apply Property_dom in H14; unfold Difference.
                apply bel_inter; rewrite H10 in H14; split; auto.
                unfold Complement; apply Axiom_Scheme; split; Ens; intro.
                apply Axiom_Scheme in H15; destruct H15.
                rewrite H16 in H13; try apply bel_universe_set; Ens.
                generalize (notin_fix u); intros; contradiction.
            - apply Axiom_Extent; split; intros.
              + unfold Range in H13; apply Axiom_Scheme in H13.
                destruct H13, H14.
                unfold Restriction in H14; apply bel_inter in H14; destruct H14.
                unfold Cartesian in H15; apply Axiom_SchemeP in H15.
                destruct H15.
                clear H15; destruct H16; clear H16; unfold Difference in H15.
                apply bel_inter in H15; destruct H15; double H15.
                rewrite <- H10 in H15; rewrite H6 in H17.
                apply bel_union in H17; destruct H17.
                * clear H17; apply Property_Value in H15; auto.
                  add ([x0,z] ∈ f) H15; apply H9 in H15; rewrite <- H15 in *.
                  clear H15; unfold Difference; apply bel_inter; double H14.
                  apply Property_ran in H15; rewrite H12 in H15; split; auto.
                  unfold Complement; apply Axiom_Scheme; split; Ens; intro.
                  apply Axiom_Scheme in H17; destruct H17; assert (u ∈ dom(f)).
                  { rewrite H10, H6; apply bel_union; right.
                    unfold Singleton; apply Axiom_Scheme; Ens. }
                  apply Property_Value in H19; auto; AssE [u,f[u]].
                  apply ord_set in H20; destruct H20.
                  rewrite H18 in H14; try apply bel_universe_set; Ens.
                  unfold Complement in H16; apply Axiom_Scheme in H16.
                  destruct H16; elim H22; unfold Singleton.
                  apply Axiom_Scheme; split; Ens; intros.
                  apply H11 with (x:= f[u]); unfold Inverse.
                  split; apply Axiom_SchemeP; split; try apply ord_set; auto.
                * unfold Complement in H16; apply Axiom_Scheme in H16.
                  destruct H16; contradiction.
              + unfold Difference in H13; apply bel_inter in H13; destruct H13.
                rewrite <- H12 in H13; apply Axiom_Scheme in H13.
                destruct H13, H15.
                unfold Range; apply Axiom_Scheme; split; Ens; exists x0.
                unfold Restriction; apply bel_inter; split; auto.
                unfold Cartesian; apply Axiom_SchemeP; split; Ens.
                split; try apply bel_universe_set; Ens; apply bel_inter; double H15.
                apply Property_dom in H16; rewrite <- H10; split; auto.
                unfold Complement; apply Axiom_Scheme; split; Ens; intro.
                apply Axiom_Scheme in H17; destruct H17.
                rewrite H18 in *; try apply bel_universe_set; Ens.
                apply Property_Value in H16; auto; clear H17 H18.
                add ([u,z] ∈ f) H16; apply H9 in H16; rewrite H16 in H14.
                unfold Complement in H14; apply Axiom_Scheme in H14; clear H13.
                destruct H14; elim H14; apply Axiom_Scheme; Ens. }
        * unfold Difference in H14; apply bel_inter in H14; destruct H14.
          apply H8; auto.
      + assert (f[u] ∈ y).
        { assert (u ∈ dom(f)).
          { rewrite H10, H6; apply bel_union; right; apply Axiom_Scheme; Ens. }
          apply Property_Value in H13; auto; apply Property_ran in H13.
          rewrite H12 in H13; auto. }
        AssE f[u]; apply sing_ele in H14; destruct H14; rewrite H15.
        clear H14 H15; apply H8; auto. }
  rewrite <- H2 in H; clear H2; apply Axiom_Scheme in H; destruct H, H2.
  apply H3; repeat split; auto.
Qed.

Hint Resolve fin_eleU : set.


(* 170 Theorem  If x and y are finite so is x×y. *)

Theorem fin_cart : forall x y,
  Finite x /\ Finite y -> Finite (x × y).
Proof.
  intros; destruct H.
  generalize (classic (y = Φ)); intros; destruct H1.
  - rewrite H1 in *; clear H1.
    assert ((x × Φ) = Φ).
    { apply Axiom_Extent; split; intros.
      - PP H1 a b; apply Axiom_SchemeP in H2; destruct H2, H3.
        generalize (not_bel_zero b); intros; contradiction.
      - generalize (not_bel_zero z); intros; contradiction. }
    rewrite H1; auto.
  - assert (∪ \{ λ u, exists v, v∈x /\ u = ([v] × y) \} = x × y).
    { clear H1; apply Axiom_Extent; split; intros.
      - unfold Element_U in H1; apply Axiom_Scheme in H1; destruct H1, H2, H2.
        apply Axiom_Scheme in H3; destruct H3, H4, H4; unfold Cartesian.
        rewrite H5 in H2; PP H2 a b; apply Axiom_SchemeP in H6; destruct H6, H7.
        apply Axiom_SchemeP; repeat split; auto; unfold Singleton in H7.
        apply Axiom_Scheme in H7; destruct H7.
        rewrite H9; try apply bel_universe_set; Ens.
      - unfold Cartesian in H1; PP H1 a b; apply Axiom_SchemeP in H2.
        destruct H2, H3; apply Axiom_Scheme.
        split; auto; exists ([a] × y); split.
        + unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
          unfold Singleton; apply Axiom_Scheme; split; Ens.
        + apply Axiom_Scheme; split; Ens; apply set_sing_cart; split; Ens.
          apply Property_Finite; auto. }
    rewrite <- H2; clear H2; apply fin_eleU; intros.
    + assert (x ≈ \{ λ u, exists v, v∈x /\ u = ([v] × y) \}).
      { unfold Equivalent; exists (\{\ λ u v, u∈x /\ v = ([u] × y) \}\).
        repeat split; intros; try (unfold Relation; intros; PP H2 a b; Ens).
        - destruct H2; apply Axiom_SchemeP in H2; apply Axiom_SchemeP in H3.
          destruct H2, H3, H4, H5; rewrite H6, H7; auto.
        - destruct H2; apply Axiom_SchemeP in H2; apply Axiom_SchemeP in H3.
          destruct H2, H3; clear H2 H3; apply Axiom_SchemeP in H4.
          apply Axiom_SchemeP in H5; destruct H4, H5, H3, H5; rewrite H7 in H6.
          clear H7; generalize (classic (y0 = z)); intros; destruct H7; auto.
          elim H7; clear H7; apply not_zero_exist_bel in H1; destruct H1.
          assert ([y0,x1] ∈ ([z] × y)).
          { rewrite H6; unfold Cartesian; apply Axiom_SchemeP.
            repeat split; try apply ord_set; Ens.
            unfold Singleton; apply Axiom_Scheme; split; Ens. }
          unfold Cartesian in H7; apply Axiom_SchemeP in H7; destruct H7, H8.
          unfold Singleton in H8; apply Axiom_Scheme in H8; destruct H8.
          apply H10; apply bel_universe_set; Ens.
        - apply Axiom_Extent; split; intros.
          + unfold Domain in H2; apply Axiom_Scheme in H2; destruct H2, H3.
            apply Axiom_SchemeP in H3; apply H3.
          + unfold Domain; apply Axiom_Scheme; split; Ens.
            exists ([z] × y); apply Axiom_SchemeP; repeat split; auto.
            apply ord_set; split; Ens; apply Property_Finite in H0.
            apply set_sing_cart; split; Ens.
        - apply Axiom_Extent; split; intros.
          + unfold Range in H2; apply Axiom_Scheme in H2; destruct H2, H3.
            apply Axiom_SchemeP in H3; destruct H3, H4.
            apply Axiom_Scheme; split; Ens.
          + apply Axiom_Scheme in H2; destruct H2, H3, H3.
            unfold Range; apply Axiom_Scheme; split; auto; exists x0.
            apply Axiom_SchemeP; repeat split; try apply ord_set; Ens. }
      assert (Ensemble x /\ Ensemble \{λ u, exists v, v∈x/\u=([v]×y)\}).
      { apply Property_Finite in H; apply Property_Finite in H0; split; auto.
        assert (Ensemble pow(x × y)).
        { apply pow_set; auto; apply set_cart; split; auto. }
        apply (sub_set pow(x × y) _); auto; unfold Subclass; intros.
        apply Axiom_Scheme in H4; destruct H4, H5, H5; rewrite H6 in *.
        clear H6; unfold PowerClass; apply Axiom_Scheme; split; auto.
        unfold Subclass; intros.
        PP H6 a b; apply Axiom_SchemeP in H7; destruct H7, H8.
        apply Axiom_SchemeP.
        repeat split; auto; unfold Singleton in H8; apply Axiom_Scheme in H8.
        destruct H8; rewrite H10; try apply bel_universe_set; Ens. }
      apply card_eq in H3; apply H3 in H2; clear H3.
      unfold Finite; unfold Finite in H; rewrite <- H2; auto.
    + apply Axiom_Scheme in H2; destruct H2, H3, H3; rewrite H4 in *; clear H4.
      assert (y ≈ ([x0] × y)).
      { unfold Equivalent; exists (\{\ λ u v, u∈y /\ v = [x0,u] \}\).
        repeat split; intros; try (unfold Relation; intros; PP H4 a b; Ens).
        - destruct H4; apply Axiom_SchemeP in H4; apply Axiom_SchemeP in H5.
          destruct H4, H5, H6, H7; rewrite H8, H9; auto.
        - destruct H4; apply Axiom_SchemeP in H4; apply Axiom_SchemeP in H5.
          destruct H4, H5; clear H4 H5; apply Axiom_SchemeP in H6.
          apply Axiom_SchemeP in H7; destruct H6, H7, H5, H7; rewrite H9 in H8.
          apply ord_eq in H8; destruct H8; Ens.
        - apply Axiom_Extent; split; intros.
          + unfold Domain in H4; apply Axiom_Scheme in H4; destruct H4, H5.
            apply Axiom_SchemeP in H5; apply H5.
          + unfold Domain; apply Axiom_Scheme; split; Ens.
            exists [x0,z0]; apply Axiom_SchemeP; repeat split; auto.
            apply ord_set; split; Ens; apply ord_set; Ens.
        - apply Axiom_Extent; split; intros.
          + unfold Range in H4; apply Axiom_Scheme in H4; destruct H4, H5.
            apply Axiom_SchemeP in H5; destruct H5, H6; rewrite H7 in *.
            clear H7; apply Axiom_SchemeP; repeat split; auto; unfold Singleton.
            apply Axiom_Scheme; split; Ens.
          + PP H4 a b; apply Axiom_SchemeP in H5; destruct H5, H6.
            unfold Range; apply Axiom_Scheme; split; auto; exists b.
            apply Axiom_SchemeP; repeat split; try apply ord_set; Ens.
            unfold Singleton in H6; apply Axiom_Scheme in H6; destruct H6.
            rewrite H8; try apply bel_universe_set; Ens. }
      assert (Ensemble y /\ Ensemble ([x0] × y)).
      { apply Property_Finite in H; apply Property_Finite in H0; Ens. }
      apply card_eq in H5; apply H5 in H4; clear H5.
      unfold Finite; unfold Finite in H0; rewrite <- H4; auto.
Qed.

Hint Resolve fin_cart : set.


(* 171 Theorem  If x is finite so is pow(x). *)

Lemma lem_fin_pow : forall x y,
  y∈x -> pow(x) = pow(x~[y]) ∪ (\{λ z, z ⊂ x /\ y ∈ z\}).
Proof.
  intros; unfold PowerClass; apply Axiom_Extent.
  split; intros; apply Axiom_Scheme in H0; destruct H0;
  apply Axiom_Scheme; split; auto.
  - generalize (classic (y ∈ z)); intros; destruct H2.
    + right; apply Axiom_Scheme; split; auto.
    + left; apply Axiom_Scheme; split; auto; unfold Subclass; intros; double H3.
      unfold Difference; apply bel_inter; apply H1 in H4; split; auto.
      unfold Complement; apply Axiom_Scheme; split; Ens; intro.
      unfold Singleton in H5; apply Axiom_Scheme in H5; destruct H5.
      rewrite H6 in H3; try contradiction; apply bel_universe_set; Ens.
  - destruct H1; apply Axiom_Scheme in H1; try apply H1; clear H0; destruct H1.
    unfold Subclass; intros; apply H1 in H2; unfold Difference in H2.
    apply bel_inter in H2; apply H2.
Qed.

Theorem fin_pow : forall (x: Class),
  Finite x -> Finite pow(x).
Proof.
  intros; double H.
  unfold Finite in H; apply Property_Finite in H0.
  assert (\{λ u, u∈W /\ (forall y, P[y] = u /\ Ensemble y -> Finite pow(y))\}
            = W).
  { apply math_ind.
    - unfold Subclass; intros; apply Axiom_Scheme in H1; apply H1.
    - apply Axiom_Scheme; generalize (zero_not_int x); intros; destruct H1.
      clear H2; repeat split; Ens; intros; destruct H2; AssE y; clear H3.
      generalize (classic (y = Φ)); intros; destruct H3.
      + assert (pow(Φ) = [Φ]).
        { unfold PowerClass, Singleton; apply Axiom_Extent.
          split; intros; apply Axiom_Scheme in H5;
          destruct H5; apply Axiom_Scheme.
          - split; auto; intros; add (Φ ⊂ z) H6; try apply zero_sub.
            apply sub_eq in H6; auto.
          - split; auto; rewrite H6; try apply bel_universe_set; Ens.
            unfold Subclass; intros; auto. }
        rewrite H3 in *; rewrite H5; apply Finite_Single; Ens.
      + apply not_zero_exist_bel in H3; destruct H3; apply card_equiv in H4.
        apply equiv_com in H4; unfold Equivalent in H4.
        destruct H4 as [f H4], H4, H4, H5; rewrite <- H5 in H3.
        apply Property_Value in H3; auto; apply Property_ran in H3.
        rewrite H7, H2 in H3; generalize (not_bel_zero f[x0]); contradiction.
    - intros; apply Axiom_Scheme in H1; apply Axiom_Scheme.
      destruct H1, H2; double H2.
      apply int_succ in H4; repeat split; Ens; intros; destruct H5.
      AssE y; clear H6; double H7; unfold PlusOne in H5; apply card_equiv in H7.
      unfold Equivalent in H7; destruct H7 as [f H7], H7, H7, H8.
      assert (u ∈ P[y]).
      { rewrite H5; apply bel_union; right; unfold Singleton.
        apply Axiom_Scheme; split; Ens. }
      double H11; rewrite <- H8 in H12; apply Property_Value in H12; auto.
      apply Property_ran in H12; rewrite H10 in H12; apply lem_fin_pow in H12.
      rewrite H12; clear H12; apply fin_union.
      assert (Finite pow(y ~ [f[u]])).
      { apply H3; assert (Ensemble (y ~ [f[u]])).
        { apply (sub_set y _); auto; unfold Subclass; intros.
          unfold Difference in H12; apply bel_inter in H12; apply H12. }
        repeat split; auto; intros; apply W_sub_C in H2.
        apply card_iff_eq in H2; clear H1; destruct H2.
        rewrite <- H2 at 2; add (Ensemble u) H12; apply card_eq in H12.
        apply H12; clear H12; apply equiv_com; unfold Equivalent.
        exists (f|(P[y]~[u])).
        { repeat split; unfold Relation; intros.
          - unfold Restriction in H12; apply bel_inter in H12.
            destruct H12; PP H13 a b; Ens.
          - unfold Restriction in H12; destruct H12; apply bel_inter in H12.
            apply bel_inter in H13; destruct H12, H13; unfold Function in H7.
            apply H7 with (x:= x0); split; auto.
          - PP H12 a b; Ens.
          - unfold Inverse, Restriction in H12; destruct H12.
            apply Axiom_SchemeP in H12; apply Axiom_SchemeP in H13.
            destruct H12, H13.
            apply bel_inter in H14; apply bel_inter in H15; destruct H14, H15.
            clear H16 H17; unfold Function in H9; apply H9 with (x:= x0).
            split; apply Axiom_SchemeP; Ens.
          - apply Axiom_Extent; split; intros.
            + unfold Domain in H12; apply Axiom_Scheme in H12.
              destruct H12, H13.
              unfold Restriction in H13; apply bel_inter in H13; destruct H13.
              clear H13; unfold Cartesian in H14; apply Axiom_SchemeP in H14.
              destruct H14, H14; clear H15; unfold Difference in H14.
              apply bel_inter in H14; destruct H14; rewrite H5 in H14.
              apply bel_union in H14; destruct H14; auto.
              apply Axiom_Scheme in H15; destruct H15; contradiction.
            + unfold Domain; apply Axiom_Scheme; split; Ens; exists f[z].
              unfold Restriction; apply bel_inter.
              assert (z ∈ dom(f)). { rewrite H8, H5; apply bel_union; tauto. }
              apply Property_Value in H13; auto; split; auto.
              unfold Cartesian; apply Axiom_SchemeP; split; Ens; double H13.
              apply Property_ran in H14; split; try apply bel_universe_set; Ens.
              clear H14; apply Property_dom in H13; unfold Difference.
              apply bel_inter; rewrite H8 in H13; split; auto.
              unfold Complement; apply Axiom_Scheme; split; Ens; intro.
              apply Axiom_Scheme in H14; destruct H14.
              rewrite H15 in H12; try apply bel_universe_set; Ens.
              generalize (notin_fix u); intros; contradiction.
          - apply Axiom_Extent; split; intros.
            + unfold Range in H12; apply Axiom_Scheme in H12; destruct H12, H13.
              unfold Restriction in H13; apply bel_inter in H13; destruct H13.
              unfold Cartesian in H14; apply Axiom_SchemeP in H14; destruct H14.
              clear H14; destruct H15; clear H15; unfold Difference in H14.
              apply bel_inter in H14; destruct H14; double H14.
              rewrite <- H8 in H14; rewrite H5 in H16.
              apply bel_union in H16; destruct H16.
              * clear H16; apply Property_Value in H14; auto.
                add ([x0,z] ∈ f) H14; apply H7 in H14; rewrite <- H14 in *.
                clear H14; unfold Difference; apply bel_inter; double H13.
                apply Property_ran in H14; rewrite H10 in H14; split; auto.
                unfold Complement; apply Axiom_Scheme; split; Ens; intro.
                apply Axiom_Scheme in H16; destruct H16; assert (u ∈ dom(f)).
                { rewrite H8, H5; apply bel_union; right.
                  unfold Singleton; apply Axiom_Scheme; Ens. }
                apply Property_Value in H18; auto; AssE [u,f[u]].
                apply ord_set in H19; destruct H19.
                rewrite H17 in H13; try apply bel_universe_set; Ens.
                unfold Complement in H15; apply Axiom_Scheme in H15.
                destruct H15.
                elim H21; unfold Singleton; apply Axiom_Scheme.
                split; Ens; intros.
                apply H9 with (x:= f[u]); unfold Inverse.
                split; apply Axiom_SchemeP; split; try apply ord_set; auto.
              * unfold Complement in H15; apply Axiom_Scheme in H15.
                destruct H15; contradiction.
            + unfold Difference in H12; apply bel_inter in H12; destruct H12.
              rewrite <- H10 in H12; apply Axiom_Scheme in H12.
              destruct H12, H14.
              unfold Range; apply Axiom_Scheme; split; Ens; exists x0.
              unfold Restriction; apply bel_inter; split; auto.
              unfold Cartesian; apply Axiom_SchemeP; split; Ens.
              split; try apply bel_universe_set; Ens; apply bel_inter; double H14.
              apply Property_dom in H15; rewrite <- H8; split; Ens.
              unfold Complement; apply Axiom_Scheme; split; Ens; intro.
              apply Axiom_Scheme in H16; destruct H16.
              rewrite H17 in *; try apply bel_universe_set; Ens.
              apply Property_Value in H15; auto; clear H16 H17.
              add ([u,z] ∈ f) H15; apply H7 in H15; rewrite H15 in H13.
              unfold Complement in H13; apply Axiom_Scheme in H13; clear H12.
              destruct H13; elim H13; apply Axiom_Scheme; Ens. } }
      split; auto.
      assert (pow(y ~ [f[u]]) ≈ \{λ z, z ⊂ y /\ f[u] ∈ z\}).
      { unfold Equivalent.
        exists (\{\ λ v w, v ∈ pow(y~[f[u]]) /\ w = v ∪ [f[u]] \}\).
        repeat split; unfold Relation; intros; try PP H13 a b; Ens.
        - destruct H13; apply Axiom_SchemeP in H13; apply Axiom_SchemeP in H14.
          destruct H13, H14, H15, H16; rewrite H17, H18; auto.
        - destruct H13; apply Axiom_SchemeP in H13; apply Axiom_SchemeP in H14.
          destruct H13, H14; clear H13 H14; apply Axiom_SchemeP in H15.
          apply Axiom_SchemeP in H16; destruct H15, H16, H14, H16.
          rewrite H18 in H17; clear H13 H15 H18; unfold PowerClass in H14, H16.
          apply Axiom_Scheme in H14; apply Axiom_Scheme in H16.
          destruct H14, H16; apply Axiom_Extent; split; intros.
          + assert (z0 ∈ (y0 ∪ [f[u]])). { apply bel_union; tauto. }
            rewrite <- H17 in H19; apply bel_union in H19; destruct H19; auto.
            apply H14 in H18; unfold Difference in H18; apply bel_inter in H18.
            destruct H18; unfold Complement in H20; apply Axiom_Scheme in H20.
            destruct H20; contradiction.
          + assert (z0 ∈ (z ∪ [f[u]])). { apply bel_union; tauto. }
            rewrite H17 in H19; apply bel_union in H19; destruct H19; auto.
            apply H16 in H18; unfold Difference in H18; apply bel_inter in H18.
            destruct H18; unfold Complement in H20; apply Axiom_Scheme in H20.
            destruct H20; contradiction.
        - unfold Domain; apply Axiom_Extent; split; intros.
          + apply Axiom_Scheme in H13; destruct H13, H14.
            apply Axiom_SchemeP in H14; apply H14.
          + apply Axiom_Scheme; split; Ens; exists (z ∪ [f[u]]).
            apply Axiom_SchemeP; repeat split; auto; apply ord_set.
            split; Ens; apply Axiom_Union; split; Ens.
            rewrite <- H8 in H11; apply Property_Value in H11; auto.
            apply Property_ran in H11; AssE f[u]; apply sing_set; auto.
        - unfold Range; apply Axiom_Extent; split; intros.
          + apply Axiom_Scheme in H13; destruct H13, H14.
            apply Axiom_SchemeP in H14.
            destruct H14, H15; apply Axiom_Scheme; split; auto; rewrite H16.
            clear H16; unfold PowerClass in H15; apply Axiom_Scheme in H15.
            destruct H15; rewrite <- H8 in H11.
            apply Property_Value in H11; auto; apply Property_ran in H11.
            rewrite H10 in H11; split.
            * unfold Subclass; intros; apply bel_union in H17; destruct H17.
              { apply H16 in H17; apply bel_inter in H17; apply H17. }
              { apply Axiom_Scheme in H17; destruct H17.
                rewrite H18; try apply bel_universe_set; Ens. }
            * apply bel_union; right; apply Axiom_Scheme; split; Ens.
          + apply Axiom_Scheme in H13; destruct H13, H14; apply Axiom_Scheme.
            split; auto; exists (z~[f[u]]); apply Axiom_SchemeP.
            assert (Ensemble (z ~ [f[u]])).
            { apply sub_set with (x:= z); auto; unfold Subclass.
              intros; apply Axiom_Scheme in H16; apply H16. }
            repeat split.
            * apply ord_set; split; auto.
            * unfold PowerClass; apply Axiom_Scheme; split; auto.
              unfold Subclass; intros; apply Axiom_Scheme in H17.
              destruct H17, H18; apply bel_inter; split; auto.
            * apply Axiom_Extent; split; intros.
              { generalize (classic (z0=f[u])); intros.
                apply bel_union; destruct H18.
                - right; apply Axiom_Scheme; split; Ens.
                - left; unfold Difference; apply bel_inter; split; auto.
                  apply Axiom_Scheme; split; Ens; intro.
                  apply Axiom_Scheme in H19.
                  destruct H19; rewrite H20 in H18; try tauto.
                  apply bel_universe_set; Ens. }
              { apply bel_union in H17; destruct H17.
                - unfold Difference in H17; apply bel_inter in H17; apply H17.
                - unfold Singleton; apply Axiom_Scheme in H17; destruct H17.
                  rewrite H18; auto; apply bel_universe_set; Ens. } }
      double H12; apply Property_Finite in H14; unfold Finite in H12.
      unfold Finite; apply card_eq in H13; try rewrite <- H13; auto.
      split; auto; clear H13 H15; apply pow_set in H6; auto.
      apply sub_set with (x:= pow(y)); auto; unfold Subclass at 1; intros.
      apply Axiom_Scheme in H13; destruct H13, H14, H15; unfold PowerClass.
      apply Axiom_Scheme; split; auto. }
  rewrite <- H1 in H; clear H1; apply Axiom_Scheme in H; destruct H, H1.
  apply H2; split; auto.
Qed.

Hint Resolve fin_pow : set.


(* 172 Theorem  If x is finite, y ⊂ x and P[y] = P[x], then x = y. *)

Theorem fin_card_eq : forall x y,
  Finite x -> y ⊂ x -> P[y] = P[x] -> x = y.
Proof.
  intros.
  double H; apply Property_Finite in H2; symmetry.
  double H; unfold Finite in H3; unfold W in H3; apply Axiom_Scheme in H3.
  destruct H3; unfold NInteger in H4; destruct H4; unfold WellOrdered in H5.
  double H2; apply card_equiv in H6; apply equiv_com in H6.
  unfold Equivalent in H6; destruct H6 as [f H6], H6, H6, H7.
  generalize (classic (y = x)); intros; destruct H10; auto.
  assert (y ⊊ x). { unfold ProperSubclass; split; auto. }
  apply Property_ProperSubclass' in H11; destruct H11 as [z H11], H11.
  generalize (classic (P[x] = Φ)); intros; destruct H13.
  - rewrite <- H7 in H11; apply Property_Value in H11; auto.
    apply Property_ran in H11; rewrite H9, H13 in H11.
    generalize (not_bel_zero f[z]); intros; contradiction.
  - assert (P[x] ⊂ P [x] /\ P[x] ≠ Φ). { split; unfold Subclass; Ens. }
    apply H5 in H14; clear H5 H13; destruct H14 as [u H5].
    assert (P[x] ∈ R /\ LastMember u E P[x]).
    { split; auto; unfold R; apply Axiom_Scheme; split; auto. }
    apply ordnum_plus_eq in H13; unfold FirstMember in H5; destruct H5; clear H14.
    assert ((x ~ [z]) ≈ u).
    { rewrite <- H9 in H5; apply Axiom_Scheme in H5; destruct H5; clear H5.
      destruct H14; rewrite <- H7 in H11; apply Property_Value in H11; auto.
      generalize (classic (z = x0)); intros; destruct H14.
      - rewrite H14; unfold Equivalent; exists (f | (x ~ [x0])).
        repeat split; unfold Relation; intros.
        + apply bel_inter in H15; destruct H15; PP H16 a b; Ens.
        + unfold Restriction in H15; destruct H15.
          apply bel_inter in H15; apply bel_inter in H16.
          destruct H15, H16; apply H6 with (x:= x1); auto.
        + PP H15 a b; Ens.
        + unfold Inverse, Restriction in H15; destruct H15.
          apply Axiom_SchemeP in H15; apply Axiom_SchemeP in H16; destruct H15, H16.
          apply bel_inter in H17; apply bel_inter in H18; destruct H17, H18.
          apply H8 with (x:= x1); unfold Inverse; split; apply Axiom_SchemeP; Ens.
        + apply Axiom_Extent; split; intros.
          * unfold Domain in H15; apply Axiom_Scheme in H15; destruct H15, H16.
            unfold Restriction in H16; apply bel_inter in H16; destruct H16.
            unfold Cartesian in H17; apply Axiom_SchemeP in H17; apply H17.
          * unfold Domain; apply Axiom_Scheme; split; Ens; exists f[z0]; double H15.
            unfold Difference in H16; apply bel_inter in H16; destruct H16.
            clear H17; rewrite <- H7 in H16; apply Property_Value in H16; auto.
            unfold Restriction; apply bel_inter; split; auto; unfold Cartesian.
            apply Axiom_SchemeP; repeat split; Ens; apply Property_ran in H16.
            apply bel_universe_set; Ens.
        + apply Axiom_Extent; split; intros.
          * unfold Range in H15; apply Axiom_Scheme in H15; destruct H15, H16.
            apply bel_inter in H16; destruct H16; double H16.
            apply Property_ran in H18; rewrite H9, H13 in H18.
            unfold PlusOne in H18; apply bel_union in H18; destruct H18; auto.
            apply Axiom_Scheme in H18; destruct H18; unfold Cartesian in H17.
            apply Axiom_SchemeP in H17; destruct H17, H20; clear H17 H18 H21.
            unfold Difference in H20; apply bel_inter in H20; destruct H20.
            clear H17; unfold Complement in H18; apply Axiom_Scheme in H18.
            destruct H18; elim H18; clear H18; unfold Singleton; apply Axiom_Scheme.
            split; auto; intros; clear H17 H18; apply H8 with (x:= u).
            AssE [x0,u]; apply ord_set in H17; destruct H17.
            rewrite H19 in H16; try apply bel_universe_set; Ens; clear H19.
            split; apply Axiom_SchemeP; split; try apply ord_set; auto.
            apply Property_dom in H16; split; Ens.
          * unfold Range; apply Axiom_Scheme; split; Ens; assert (z0 ∈ ran(f)).
            { rewrite H9, H13; unfold PlusOne; apply bel_union; tauto. }
            unfold Range in H16; apply Axiom_Scheme in H16; destruct H16, H17.
            exists x1; unfold Restriction; apply bel_inter; split; auto.
            unfold Cartesian; apply Axiom_SchemeP; split; Ens; double H17.
            split; try apply bel_universe_set; auto; unfold Difference.
            apply Property_dom in H18; rewrite H7 in H18; apply bel_inter.
            split; auto; unfold Complement; apply Axiom_Scheme; split; Ens; intro.
            unfold Singleton in H19; apply Axiom_Scheme in H19; destruct H19.
            double H5; apply Property_dom in H21; clear H18 H19.
            rewrite H20 in H17; try apply bel_universe_set; Ens; clear H20 H21.
            add ([x0,z0] ∈ f) H5; apply H6 in H5; clear H17.
            rewrite H5 in H15; generalize (notin_fix z0); contradiction.
      - unfold Equivalent; exists (\{\ λ v w, v ∈ (x ~ [z]) /\
        (v = x0 -> w = f[z]) /\ (v <> x0 -> [v,w] ∈ f) \}\).
        repeat split; unfold Relation; intros; try PP H15 a b; Ens.
        + destruct H15; apply Axiom_SchemeP in H15; apply Axiom_SchemeP in H16.
          destruct H15, H16, H17, H18; generalize (classic (x1 = x0)); intros.
          destruct H21; double H21; apply H19 in H21; apply H20 in H22.
          * rewrite H21, H22; auto.
          * apply H6 with (x:= x1); auto.
        + destruct H15; apply Axiom_SchemeP in H15; apply Axiom_SchemeP in H16.
          destruct H15, H16; apply Axiom_SchemeP in H17; apply Axiom_SchemeP in H18.
          destruct H17, H18; clear H17 H18; destruct H19, H20.
          apply bel_inter in H17; apply bel_inter in H19; destruct H17, H19.
          generalize (classic (y0 = x0)) (classic (z0 = x0)); intros.
          destruct H23, H24; try rewrite H23, H24; apply H18 in H23;
          apply H20 in H24; clear H18 H20; auto.
          * rewrite <- H23 in H11; clear H23.
            assert ([x1,z] ∈ f⁻¹ /\ [x1,z0] ∈ f⁻¹).
            { unfold Inverse; split; apply Axiom_SchemeP; split; Ens.
              AssE [z,x1]; apply ord_set; apply ord_set in H18; tauto. }
            apply H8 in H18; rewrite <- H18 in H22; clear H18 H24.
            apply Axiom_Scheme in H22; destruct H22; elim H20; apply Axiom_Scheme; Ens.
          * rewrite <- H24 in H11; clear H24.
            assert ([x1,z] ∈ f⁻¹ /\ [x1,y0] ∈ f⁻¹).
            { unfold Inverse; split; apply Axiom_SchemeP; split; Ens.
              AssE [z,x1]; apply ord_set; apply ord_set in H18; tauto. }
            apply H8 in H18; rewrite <- H18 in H21; clear H16 H18 H19 H22 H23.
            apply Axiom_Scheme in H21; destruct H21; elim H18; apply Axiom_Scheme; Ens.
          * apply H8 with (x:= x1); split; apply Axiom_SchemeP; split; auto.
        + apply Axiom_Extent; split; intros.
          * unfold Domain in H15; apply Axiom_Scheme in H15; destruct H15, H16.
            apply Axiom_SchemeP in H16; apply H16.
          * unfold Domain; apply Axiom_Scheme; split; Ens.
            generalize (classic (z0 = x0)); intros; destruct H16.
            { exists f[z]; apply Axiom_SchemeP; repeat split; intros; try tauto.
              apply Property_ran in H11; apply ord_set; split; Ens. }
            { exists f[z0]; double H15; apply bel_inter in H17; destruct H17.
              rewrite <- H7 in H17; apply Property_Value in H17; auto.
              apply Axiom_SchemeP; repeat split; intros; try tauto; Ens. }
        + apply Axiom_Extent; split; intros.
          * unfold Range in H15; apply Axiom_Scheme in H15; destruct H15, H16.
            apply Axiom_SchemeP in H16; destruct H16, H17.
            generalize (classic (x1 = x0)); intros; destruct H19.
            { apply H18 in H19; clear H18; rewrite H19; double H11.
              apply Property_ran in H18; rewrite H9, H13 in H18.
              apply bel_union in H18; destruct H18; auto; AssE [x0, u].
              apply ord_set in H20; destruct H20; apply Axiom_Scheme in H18.
              destruct H18; rewrite H22 in H11; try apply bel_universe_set; auto.
              elim H14; apply H8 with (x:= u); unfold Inverse.
              split; apply Axiom_SchemeP; split; try apply ord_set; Ens.
              apply Property_dom in H11; split; Ens. }
            { double H19; apply H18 in H20; clear H18; double H20.
              apply Property_ran in H20; rewrite H9, H13 in H20; clear H15.
              apply bel_union in H20; destruct H20; auto; apply Axiom_Scheme in H15.
              destruct H15; AssE [x0,u]; apply ord_set in H21; destruct H21.
              rewrite H20 in H18; try apply bel_universe_set; Ens; clear H20.
              elim H19; apply H8 with (x:= u); unfold Inverse.
              split; apply Axiom_SchemeP; split; try apply ord_set; Ens. }
          * unfold Range; apply Axiom_Scheme; split; Ens.
            assert (z0 ∈ ran(f)). { rewrite H9, H13; apply bel_union; tauto. }
            unfold Range in H16; apply Axiom_Scheme in H16; destruct H16, H17.
            generalize (classic (z0 = f[z])); intros; destruct H18.
            { exists x0; apply Property_dom in H5; apply Axiom_SchemeP.
              repeat split; intros; try tauto; try apply ord_set; Ens.
              rewrite H7 in H5; unfold Difference; apply bel_inter; split; auto.
              unfold Complement; apply Axiom_Scheme; split; Ens; intro.
              unfold Singleton in H19; apply Axiom_Scheme in H19; destruct H19.
              apply Property_dom in H11; rewrite H20 in H14; try tauto.
              apply bel_universe_set; Ens. }
            { exists x1; apply Axiom_SchemeP; repeat split; intros; Ens.
              - double H17; apply Property_dom in H19; rewrite H7 in H19.
                unfold Difference; apply bel_inter; split; auto.
                apply Axiom_Scheme; split; Ens; intro; apply Axiom_Scheme in H20.
                destruct H20; elim H18; apply H6 with (x:= z).
                rewrite H21 in H17; try split; auto; apply bel_universe_set.
                apply Property_dom in H11; Ens.
              - rewrite H19 in H17; add ([x0,z0] ∈ f) H5; apply H6 in H5.
                rewrite H5 in H15; generalize (notin_fix z0); contradiction. }}
    assert (Ensemble (x ~ [z]) /\ y ⊂ (x ~ [z])).
    { split.
      - apply (sub_set x _); auto; unfold Subclass; intros.
        unfold Difference in H15; apply bel_inter in H15; apply H15.
      - unfold Subclass, Difference; intros; apply bel_inter; split; auto.
        unfold Complement; apply Axiom_Scheme; split; Ens; unfold Singleton; intro.
        apply Axiom_Scheme in H16; destruct H16; rewrite H17 in H15; try contradiction.
        apply bel_universe_set; Ens. }
    elim H15; intros; apply card_le in H15; rewrite H1, H13 in H15.
    clear H17; add (Ensemble u) H16; Ens; apply card_eq in H16.
    apply H16 in H14; rewrite H14 in H15; clear H3 H13 H14 H16.
    unfold Finite in H; unfold W in H; apply Axiom_Scheme in H; destruct H.
    AssE u; apply int_bel_int in H5; auto.
    assert (u ∈ C). { apply W_sub_C; apply Axiom_Scheme; split; auto. }
    clear H5 H13; apply card_iff_eq in H14; destruct H14; rewrite H13 in H15.
    assert (u ∈ (u ∪ [u])). { apply bel_union; right; apply Axiom_Scheme; Ens. }
    clear H5 H13; unfold PlusOne, LessEqual in H15; destruct H15.
    + generalize (not_bel_and (u ∪ [u]) u); intros; destruct H13; auto.
    + rewrite H5 in H14; generalize (notin_fix u); contradiction.
Qed.

Hint Resolve fin_card_eq : set.


(* 173 Theorem  If x is a set and x is not finite, then there is a subset y of
   x such that y≠x and x≈y. *)

Lemma lem_notfin_exist_sub_eq : forall x0 x,
  x0 ∈ P [x] -> ~ x0 ∈ W -> x0 ∈ (P [x] ~ W).
Proof.
  intros; unfold Difference; apply bel_inter; split; auto.
  unfold Complement; apply Axiom_Scheme; split; Ens.
Qed.

Theorem notfin_exist_sub_eq : forall x,
  Ensemble x /\ ~ Finite x -> (exists y, y ⊂ x /\ y ≠ x /\ x ≈ y).
Proof.
  intros; destruct H.
  assert (W ⊂ P[x]).
  { unfold Subclass; intros; double H; apply Property_PClass in H2.
    unfold W in H1; unfold C in H2; apply Axiom_Scheme in H1; apply Axiom_Scheme in H2.
    destruct H1, H2, H4; clear H5; unfold Ordinal_Number in H4; double H3.
    unfold NInteger in H5; destruct H5; apply Axiom_Scheme in H4; clear H2 H6.
    destruct H4; add (Ordinal z) H4; clear H5; apply ord_bel_eq in H4.
    destruct H4 as [H4 | [H4 | H4]]; auto.
    - apply int_bel_int in H4; auto; destruct H0; unfold Finite.
      unfold W; apply Axiom_Scheme; split; auto.
    - destruct H0; unfold Finite; rewrite H4; apply Axiom_Scheme; Ens. }
  assert (P[x] ≈ (P[x] ~ [Φ])).
  { unfold Equivalent; exists (\{\ λ u v, u ∈ P[x] /\ ((u ∈ W -> v = PlusOne u)
    /\ (u ∈ (P[x] ~ W) -> v = u)) \}\).
    repeat split; unfold Relation; intros; try PP H2 a b; Ens.
    - destruct H2; apply Axiom_SchemeP in H2.
      apply Axiom_SchemeP in H3; destruct H2, H3, H4, H5.
      generalize (classic (x0 ∈ W)); intros; destruct H8.
      + double H8; apply H6 in H8; apply H7 in H9; rewrite H8, H9; auto.
      + apply lem_notfin_exist_sub_eq in H5; auto; clear H8; double H5.
        apply H6 in H5; apply H7 in H8; rewrite H5, H8; auto.
    - destruct H2; apply Axiom_SchemeP in H2.
      apply Axiom_SchemeP in H3; destruct H2, H3; apply Axiom_SchemeP in H4.
      apply Axiom_SchemeP in H5; destruct H4, H5, H6, H7.
      generalize (classic (y ∈ W)) (classic (z ∈ W)); intros; destruct H10, H11.
      + apply int_succ_eq; auto; apply H8 in H10; apply H9 in H11.
        rewrite H10 in H11; auto.
      + double H10; apply lem_notfin_exist_sub_eq in H7; auto; apply H8 in H10; apply H9 in H7.
        rewrite H7 in H10; rewrite H10 in H11; apply int_succ in H12; tauto.
      + double H11; apply lem_notfin_exist_sub_eq in H6; auto; apply H8 in H6; apply H9 in H11.
        rewrite H6 in H11; rewrite H11 in H10; apply int_succ in H12; tauto.
      + apply lem_notfin_exist_sub_eq in H6; apply lem_notfin_exist_sub_eq in H7; auto.
        apply H8 in H6; apply H9 in H7; rewrite <- H6, <- H7; auto.
    - apply Axiom_Extent; split; intros.
      + unfold Domain in H2; apply Axiom_Scheme in H2; destruct H2, H3.
        apply Axiom_SchemeP in H3; apply H3.
      + unfold Domain; apply Axiom_Scheme; split; Ens.
        generalize (classic (z ∈ W)); intros; destruct H3.
        * exists (PlusOne z); apply Axiom_SchemeP; repeat split; intros; auto.
          { apply int_succ in H3; apply ord_set; split; Ens. }
          { unfold Difference in H4; apply bel_inter in H4; destruct H4.
            apply Axiom_Scheme in H5; destruct H5; contradiction. }
        * exists z; apply Axiom_SchemeP; repeat split; try apply ord_set; Ens.
          intros; contradiction.
    - apply Axiom_Extent; split; intros.
      + unfold Range in H2; apply Axiom_Scheme in H2; destruct H2, H3.
        apply Axiom_SchemeP in H3; destruct H3, H4.
        generalize (classic (x0 ∈ W)); intros; destruct H6.
        * double H6; apply H5 in H7; clear H5; double H6; double H6.
          apply int_succ in H6; apply zero_not_int in H8; rewrite H7 in *.
          clear H7; apply H1 in H6; unfold Difference; apply bel_inter.
          split; auto; unfold Complement; apply Axiom_Scheme; split; Ens.
          intro; apply Axiom_Scheme in H7; destruct H7; rewrite H9 in H8; auto.
          apply bel_universe_set; Ens; exists W; apply zero_not_int; auto.
        * double H4; apply lem_notfin_exist_sub_eq in H7; auto; apply H5 in H7; clear H5.
          rewrite H7 in *; clear H7; unfold Difference; apply bel_inter.
          split; auto; unfold Complement; apply Axiom_Scheme; split; Ens.
          intro; apply Axiom_Scheme in H5; clear H2; destruct H5.
          generalize (zero_not_int x0); intros; destruct H7; clear H8.
          rewrite H5 in H6; try apply bel_universe_set; Ens.
      + unfold Difference in H2; apply bel_inter in H2; destruct H2.
        unfold Complement in H3; apply Axiom_Scheme in H3; destruct H3.
        unfold Range; apply Axiom_Scheme; split; Ens.
        generalize (classic (z ∈ W)); intros; destruct H5.
        * unfold W in H5; apply Axiom_Scheme in H5; destruct H5; double H6.
          unfold NInteger in H7; destruct H7, H8; clear H8.
          assert (z ⊂ z /\ z ≠ Φ).
          { split; unfold Subclass; intros; auto; intro; destruct H4.
            generalize (zero_not_int z); intros; destruct H4; rewrite H8.
            clear H8 H10; apply Axiom_Scheme; split; Ens. }
          apply H9 in H8; clear H9; destruct H8.
          assert (z ∈ R /\ LastMember x0 E z).
          { split; auto; try apply Axiom_Scheme; Ens. }
          apply ordnum_plus_eq in H9; unfold FirstMember in H8; destruct H8.
          AssE x0; apply int_bel_int in H8; auto; clear H10; exists x0.
          apply Axiom_SchemeP; repeat split; intros; try apply ord_set; Ens.
          -- apply H1; apply Axiom_Scheme; Ens.
          -- unfold Difference in H10; apply bel_inter in H10; destruct H10.
             unfold Complement in H12; apply Axiom_Scheme in H12; destruct H12, H13.
             unfold W; apply Axiom_Scheme; split; auto.
        * exists z; apply Axiom_SchemeP; repeat split; try apply ord_set; Ens.
          intros; contradiction. }
  double H; apply card_equiv in H3; unfold Equivalent in H3.
  destruct H3 as [f H3], H3, H3, H4.
  assert (P[x] ~ [Φ] ≈ ran(f | (P[x] ~ [Φ]))).
  { unfold Equivalent; exists (f | (P[x] ~ [Φ])).
    repeat split; unfold Relation; intros; try PP H7 a b; Ens.
    - unfold Restriction in H7; apply bel_inter in H7; destruct H7.
      PP H8 a b; Ens.
    - unfold Restriction in H7; destruct H7; apply bel_inter in H7.
      apply bel_inter in H8; destruct H7, H8; apply H3 with (x:= x0); auto.
    - unfold Restriction, Inverse in H7; destruct H7; apply Axiom_SchemeP in H7.
      apply Axiom_SchemeP in H8; destruct H7, H8; apply bel_inter in H9.
      apply bel_inter in H10; destruct H9, H10; apply H5 with (x:= x0).
      unfold Inverse; split; apply Axiom_SchemeP; split; Ens.
    - apply Axiom_Extent; split; intros.
      + unfold Domain in H7; apply Axiom_Scheme in H7; destruct H7, H8.
        unfold Restriction in H8; apply bel_inter in H8; destruct H8.
        unfold Cartesian in H9; apply Axiom_SchemeP in H9; apply H9.
      + unfold Domain; apply Axiom_Scheme; split; Ens; exists f[z].
        unfold Restriction; apply bel_inter; double H7; unfold Difference in H8.
        apply bel_inter in H8; destruct H8; clear H9; rewrite <- H4 in H8.
        apply Property_Value in H8; auto; split; auto; unfold Cartesian.
        apply Axiom_SchemeP; AssE ([z,f[z]]); apply Property_ran in H8.
        repeat split; Ens; apply bel_universe_set; Ens. }
  double H; apply card_equiv in H8; apply equiv_com in H8.
  apply equiv_tran with (z:= P[x] ~ [Φ]) in H8; auto; clear H2.
  apply equiv_tran with (z:= ran(f | (P[x] ~ [Φ]))) in H8; auto; clear H7.
  exists ran(f | (P[x] ~ [Φ])); repeat split; auto.
  - unfold Subclass; intros; unfold Range, Restriction in H2.
    apply Axiom_Scheme in H2; destruct H2, H7; apply bel_inter in H7; destruct H7.
    apply Property_ran in H7; rewrite H6 in H7; auto.
  - generalize (zero_not_int x); intros; destruct H2; clear H7; apply H1 in H2.
    rewrite <- H4 in H2; apply Property_Value in H2; auto; intro.
    assert (f[Φ] ∈ ran(f | (P[x] ~ [Φ]))).
    { rewrite H7; apply Property_ran in H2; rewrite H6 in H2; auto. }
    unfold Range in H9; apply Axiom_Scheme in H9; destruct H9, H10.
    unfold Restriction in H10; apply bel_inter in H10; destruct H10.
    assert ([f[Φ],Φ] ∈ f⁻¹ /\ [f[Φ],x0] ∈ f⁻¹).
    { AssE [Φ,f[Φ]]; AssE [x0,f[Φ]]; apply ord_set in H12.
      apply ord_set in H13; destruct H12, H13; clear H14 H15.
      split; apply Axiom_SchemeP; split; try apply ord_set; auto. }
    apply H5 in H12; rewrite H12 in H11; clear H12; unfold Cartesian in H11.
    apply Axiom_SchemeP in H11; destruct H11, H12; clear H11 H13.
    unfold Difference in H12; apply bel_inter in H12; destruct H12.
    unfold Complement in H12; apply Axiom_Scheme in H12; destruct H12, H13.
    unfold Singleton; apply Axiom_Scheme; split; Ens.
Qed.

Hint Resolve notfin_exist_sub_eq : set.


(* 174 Theorem  If x ∈ (R ~ W), then P[x+1] = P[x]. *)

Lemma le_tran_eq : forall x y, x ≼ y -> y ≼ x -> x = y.
Proof.
  intros; unfold LessEqual in H, H0; destruct H, H0; auto.
  generalize (not_bel_and x y); intros; destruct H1; auto.
Qed.

Theorem notint_card_plus_eq : forall x,
  x ∈ (R ~ W) -> P[ PlusOne x ] = P[x].
Proof.
  intros.
  unfold Difference in H; apply bel_inter in H; destruct H.
  double H; apply ordnum_succ_ordnum in H1; AssE (PlusOne x).
  add (x⊂(PlusOne x)) H2; try (unfold Subclass; intros; apply bel_union; tauto).
  apply card_le in H2; apply Axiom_Scheme in H0; destruct H0.
  assert (Ensemble x /\ ~ Finite x).
  { split; auto; clear H1 H2; unfold Finite; intro; destruct H3.
    generalize (Property_W); intros; unfold R in H; apply Axiom_Scheme in H.
    clear H0; destruct H; assert (Ordinal W /\ Ordinal x); auto; double H3.
    apply ord_bel_eq in H3; apply ord_sub_iff_le in H4.
    destruct H3 as [H3 | [H3 | H3]]; auto.
    - assert (W ≼ x); unfold LessEqual; try tauto; apply H4 in H5; clear H4.
      assert (Ensemble x /\ W ⊂ x); auto; apply card_le in H4.
      double H1; unfold W in H6; apply Axiom_Scheme in H6; destruct H6.
      unfold NInteger in H7; destruct H7; clear H8.
      assert (Ordinal P[x] /\ Ordinal W); auto; apply ord_sub_iff_le in H8.
      assert (P[x] ≼ W); unfold LessEqual; try auto; apply H8 in H9; clear H8.
      assert (Ensemble W /\ P [x] ⊂ W); Ens; apply card_le in H8; clear H9.
      rewrite card_eq_inv in H8. apply le_tran_eq in H8; auto.
      rewrite <- H8 in H1; clear H4 H8; generalize W_bel_C; intros.
      apply card_iff_eq in H4; destruct H4; rewrite H8 in H1.
      generalize (notin_fix W); intros; contradiction.
    - rewrite H3 in H1; generalize W_bel_C; intros; rewrite H3 in H5.
      apply card_iff_eq in H5; destruct H5; rewrite H6 in H1.
      generalize (notin_fix x); intros; contradiction. }
  apply notfin_exist_sub_eq in H4; destruct H4 as [u H4], H4, H5.
  assert (P[PlusOne x] ≼ P[x]).
  { assert (u ⊊ x). { split; auto. } apply Property_ProperSubclass' in H7.
    destruct H7 as [z H7], H7, H6 as [f H6], H6, H6, H9.
    assert (PlusOne x ≈ ran(\{\ λ v w, (v∈x /\ w=f[v]) \/ (v=x /\ w=z) \}\)).
    { unfold Equivalent; exists (\{\λ v w, (v∈x /\ w=f[v]) \/ (v=x /\ w=z)\}\).
      repeat split; unfold Relation; intros; try PP H12 a b; Ens.
      - destruct H12; apply Axiom_SchemeP in H12; apply Axiom_SchemeP in H13.
        destruct H12, H13, H14, H15, H14, H15; try rewrite H16, H17; auto.
        + rewrite H15 in H14; generalize (notin_fix x); contradiction.
        + rewrite H14 in H15; generalize (notin_fix x); contradiction.
      - destruct H12; apply Axiom_SchemeP in H12; apply Axiom_SchemeP in H13.
        destruct H12, H13; apply Axiom_SchemeP in H14; apply Axiom_SchemeP in H15.
        destruct H14, H15, H16, H17, H16, H17.
        + rewrite <- H9 in H16, H17; apply Property_Value in H16; auto.
          apply Property_Value in H17; auto; rewrite H19 in *; clear H19.
          rewrite H18 in *; clear H18; apply H10 with (x:= f[y]).
          unfold Inverse; split; apply Axiom_SchemeP; Ens.
        + rewrite <- H9 in H16; apply Property_Value in H16; auto.
          apply Property_ran in H16; rewrite H11 in H16; rewrite <- H18 in H16.
          rewrite H19 in H16; contradiction.
        + rewrite <- H9 in H17; apply Property_Value in H17; auto.
          apply Property_ran in H17; rewrite H11 in H17; rewrite <- H19 in H17.
          rewrite H18 in H17; contradiction.
        + rewrite H16, H17; auto.
      - apply Axiom_Extent; split; intros.
        + unfold PlusOne; apply bel_union; unfold Domain in H12.
          apply Axiom_Scheme in H12; destruct H12, H13; apply Axiom_SchemeP in H13.
          destruct H13, H14; destruct H14; try tauto; rewrite H14 in *.
          right; unfold Singleton; apply Axiom_Scheme; split; Ens.
        + unfold Domain; apply Axiom_Scheme; split; Ens; unfold PlusOne in H12.
          apply bel_union in H12; destruct H12.
          * double H12; rewrite <- H9 in H13; apply Property_Value in H13; auto.
            exists f[z0]; apply Axiom_SchemeP; repeat split; intros; Ens.
          * exists z; apply Axiom_SchemeP; split; try apply ord_set; Ens.
            right; split; auto; unfold Singleton in H12; apply Axiom_Scheme in H12.
            apply H12; apply bel_universe_set; auto. }
    assert (Ensemble x /\ ran(\{\λ v w, (v∈x/\w=f[v]) \/ (v=x/\w=z) \}\) ⊂ x).
    { split; auto; unfold Subclass; intros; apply Axiom_Scheme in H13.
      destruct H13, H14; apply Axiom_SchemeP in H14; destruct H14, H15, H15.
      - rewrite H16; rewrite <- H9 in H15; apply Property_Value in H15; auto.
        apply Property_ran in H15; rewrite H11 in H15; auto.
      - rewrite H16; auto. }
    clear H0; elim H13; intros; apply card_le in H13.
    apply card_eq in H12; try (split; Ens; apply (sub_set x _); auto).
    rewrite <- H12 in H13; clear H12 H14; auto. }
  apply le_tran_eq; auto.
Qed.

Hint Resolve notint_card_plus_eq : set.


(* 175 Definition  max[x,y] = x ∪ y. *)

Definition Max x y : Class := x ∪ y.

Corollary Property_Max : forall x y,
  (Ordinal x -> Ordinal y -> x ∈ y -> Max x y = y) /\ (x = y -> Max x y = y).
Proof.
  split; intros; try (rewrite H; unfold Max; apply union_fix).
  assert (x ≼ y); unfold LessEqual; try tauto.
  apply ord_sub_iff_le in H2; auto; unfold Max; apply union_sub; auto.
Qed.

Corollary Equal_Max : forall x y, Max x y = Max y x.
Proof.
  intros; unfold Max; apply union_com.
Qed.

Hint Unfold Max : set.
Hint Resolve Property_Max : set.
Hint Rewrite Equal_Max : set.


(* 176 Definition  《 = { z : for some [u,v] in R×R and some [x,y] in R×R,
   z=[[u,v],[x,y]], and max[u,v] < max[x,y], or max[u,v] = max[x,y] and u<x,
   or max[u,v] = max[x,y] and u=x and v<y }. *)

Definition LessLess : Class :=
  \{ λ z, exists u v x y, [u,v]∈(R×R) /\ [x,y]∈(R×R) /\ z = [[u,v],[x,y]] /\
  ((Max u v ≺ Max x y) \/ (Max u v = Max x y /\ u ≺ x) \/ (Max u v = Max x y /\
  u = x /\ v ≺ y)) \}.

Notation "≪" := (LessLess) (at level 0, no associativity).

Hint Unfold LessLess : set.


(* 177 Theorem  《 well-orders R × R. *)

Definition En_y y : Class := \{ λ z, exists u v, [u,v] ∈ y /\ z = Max u v \}.

Definition En_v v y : Class := \{ λ z, [z,v] ∈ y /\ z ∈ v \}.

Definition En_u u y : Class := \{ λ z, [u,z] ∈ y /\ z ∈ u \}.

Lemma lem_well_cartR_bd : forall a b c d,
  [a, b] ∈ R × R -> [c, d] ∈ R × R -> Ensemble a -> Ensemble b ->
  Ensemble c -> Ensemble d -> Ordinal a -> Ordinal b -> Ordinal c ->
  Ordinal d -> Max a b = b -> Max c d = d ->
  Rrelation ([a,b]) ≪ ([c,d]) \/ Rrelation ([c,d]) ≪ ([a,b]) \/ [a,b] = [c,d].
Proof.
  intros.
  assert (Ordinal b /\ Ordinal d); auto; apply ord_bel_eq in H11.
  destruct H11 as [H11 | [H11 | H11]].
  - left; unfold Rrelation, LessLess; apply Axiom_Scheme.
    split; try (apply ord_set; split; apply ord_set; auto).
    exists a, b, c, d; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - right; left; unfold Rrelation, LessLess; apply Axiom_Scheme.
    split; try (apply ord_set; split; apply ord_set; auto).
    exists c, d, a, b; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - assert (Ordinal a /\ Ordinal c); auto; apply ord_bel_eq in H12.
    destruct H12 as [H12 | [H12 | H12]].
    { left; unfold Rrelation, LessLess; apply Axiom_Scheme.
      split; try (apply ord_set; split; apply ord_set; auto).
      exists a, b, c, d; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; left; unfold Rrelation, LessLess; apply Axiom_Scheme.
      split; try (apply ord_set; split; apply ord_set; auto).
      exists c, d, a, b; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; right; rewrite H11, H12; auto. }
Qed.

Lemma lem_well_cartR_bc : forall a b c d,
  [a, b] ∈ R × R -> [c, d] ∈ R × R -> Ensemble a -> Ensemble b ->
  Ensemble c -> Ensemble d -> Ordinal a -> Ordinal b -> Ordinal c ->
  Ordinal d -> Max a b = b -> Max c d = c ->
  Rrelation ([a,b]) ≪ ([c,d]) \/ Rrelation ([c,d]) ≪ ([a,b]) \/ [a,b] = [c,d].
Proof.
  intros; assert (Ordinal b /\ Ordinal c); auto.
  apply ord_bel_eq in H11; destruct H11 as [H11 | [H11 | H11]].
  - left; unfold Rrelation, LessLess; apply Axiom_Scheme.
    split; try (apply ord_set; split; apply ord_set; auto).
    exists a, b, c, d; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - right; left; unfold Rrelation, LessLess; apply Axiom_Scheme.
    split; try (apply ord_set; split; apply ord_set; auto).
    exists c, d, a, b; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - assert (Ordinal a /\ Ordinal c); auto; apply ord_bel_eq in H12.
    destruct H12 as [H12 | [H12 | H12]].
    { left; unfold Rrelation, LessLess; apply Axiom_Scheme.
      split; try (apply ord_set; split; apply ord_set; auto).
      exists a, b, c, d; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; left; unfold Rrelation, LessLess; apply Axiom_Scheme.
      split; try (apply ord_set; split; apply ord_set; auto).
      exists c, d, a, b; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { assert (Ordinal b /\ Ordinal d); auto; apply ord_bel_eq in H13.
      destruct H13 as [H13 | [H13 | H13]].
      - left; unfold Rrelation, LessLess; apply Axiom_Scheme.
        split; try (apply ord_set; split; apply ord_set; auto).
        exists a, b, c, d; repeat split; auto; right; right.
        rewrite H9, H10; unfold Less; auto.
      - right; left; unfold Rrelation, LessLess; apply Axiom_Scheme.
        split; try (apply ord_set; split; apply ord_set; auto).
        exists c, d, a, b; repeat split; auto; right; right.
        rewrite H9, H10; unfold Less; auto.
      - right; right; rewrite H12, H13; auto. }
Qed.

Lemma lem_well_cartR_ac : forall a b c d,
  [a, b] ∈ R × R -> [c, d] ∈ R × R -> Ensemble a -> Ensemble b ->
  Ensemble c -> Ensemble d -> Ordinal a -> Ordinal b -> Ordinal c ->
  Ordinal d -> Max a b = a -> Max c d = c ->
  Rrelation ([a,b]) ≪ ([c,d]) \/ Rrelation ([c,d]) ≪ ([a,b]) \/ [a,b] = [c,d].
Proof.
  intros; assert (Ordinal a /\ Ordinal c); auto.
  apply ord_bel_eq in H11; destruct H11 as [H11 | [H11 | H11]].
  - left; unfold Rrelation, LessLess; apply Axiom_Scheme.
    split; try (apply ord_set; split; apply ord_set; auto).
    exists a, b, c, d; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - right; left; unfold Rrelation, LessLess; apply Axiom_Scheme.
    split; try (apply ord_set; split; apply ord_set; auto).
    exists c, d, a, b; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - assert (Ordinal b /\ Ordinal d); auto; apply ord_bel_eq in H12.
    destruct H12 as [H12 | [H12 | H12]].
    { left; unfold Rrelation, LessLess; apply Axiom_Scheme.
      split; try (apply ord_set; split; apply ord_set; auto).
      exists a, b, c, d; repeat split; auto; right; right.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; left; unfold Rrelation, LessLess; apply Axiom_Scheme.
      split; try (apply ord_set; split; apply ord_set; auto).
      exists c, d, a, b; repeat split; auto; right; right.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; right; rewrite H11, H12; auto. }
Qed.

Lemma lem_well_cartR_v : forall x y u v,
  x ∈ y -> y ⊂ (R × R) -> Max u v = v -> Rrelation x ≪ ([u,v]) ->
  (exists a b, [a, b] ∈ y /\ Ensemble a /\ Ordinal a /\ Ensemble b /\ Ordinal b
  /\ ((Max a b) ∈ v \/ Max a b = v /\ a ∈ u \/ Max a b = v /\ a = u /\ b ∈ v)).
Proof.
  intros.
  double H; apply H0 in H3; unfold Cartesian in H3; clear H0.
  PP H3 a b; apply Axiom_SchemeP in H0; clear H3; exists a, b; split; auto.
  destruct H0, H3; apply Axiom_Scheme in H3; apply Axiom_Scheme in H4; clear H0.
  destruct H3, H4; unfold Rrelation, LessLess in H2; apply Axiom_Scheme in H2.
  destruct H2, H6, H6, H6, H6, H6, H7, H8; clear H6 H7; apply ord_set in H2.
  destruct H2; clear H2; apply ord_set in H6; destruct H6; unfold Less in H9.
  apply ord_eq in H8; try (split; Ens; apply ord_set; Ens).
  destruct H8; apply ord_eq in H7; apply ord_eq in H8; auto.
  destruct H7, H8; rewrite <- H7, <- H8, <- H10, <- H11, H1 in H9; Ens.
Qed.

Lemma lem_well_cartR_u : forall x y u v,
  x ∈ y -> y ⊂ (R × R) -> Max u v = u -> Rrelation x ≪ ([u,v]) ->
  (exists a b, [a, b] ∈ y /\ Ensemble a /\ Ordinal a /\ Ensemble b /\ Ordinal b
  /\ ((Max a b) ∈ u \/ Max a b = u /\ a ∈ u \/ Max a b = u /\ a = u /\ b ∈ v)).
Proof.
  intros.
  double H; apply H0 in H3; unfold Cartesian in H3; clear H0.
  PP H3 a b; apply Axiom_SchemeP in H0; clear H3; exists a, b; split; auto.
  destruct H0, H3; apply Axiom_Scheme in H3; apply Axiom_Scheme in H4; clear H0.
  destruct H3, H4; unfold Rrelation, LessLess in H2; apply Axiom_Scheme in H2.
  destruct H2, H6, H6, H6, H6, H6, H7, H8; clear H6 H7; apply ord_set in H2.
  destruct H2; clear H2; apply ord_set in H6; destruct H6; unfold Less in H9.
  apply ord_eq in H8; try (split; Ens; apply ord_set; Ens).
  destruct H8; apply ord_eq in H7; apply ord_eq in H8; auto.
  destruct H7, H8; rewrite <- H7, <- H8, <- H10, <- H11, H1 in H9; Ens.
Qed.

Theorem well_order_cartR : WellOrdered ≪ (R × R).
Proof.
  unfold WellOrdered; split; intros.
  - unfold Connect; intros; destruct H; double H; double H0; PP H1 a b.
    PP H2 c d; clear H1 H2; apply Axiom_SchemeP in H3; apply Axiom_SchemeP in H4.
    destruct H3, H4; clear H1 H3; destruct H2, H4; unfold R in H1, H2, H3, H4.
    apply Axiom_Scheme in H1; apply Axiom_Scheme in H2; apply Axiom_Scheme in H3.
    apply Axiom_Scheme in H4; destruct H1, H2, H3, H4.
    assert (Ordinal a /\ Ordinal b); assert (Ordinal c /\ Ordinal d); auto.
    apply ord_bel_eq in H9; apply ord_bel_eq in H10.
    destruct H9 as [H9 | [H9 | H9]], H10 as [H10 | [H10 | H10]];
    apply Property_Max in H9; apply Property_Max in H10; auto.
    + apply lem_well_cartR_bd; auto.
    + rewrite Equal_Max in H10; apply lem_well_cartR_bc; auto.
    + apply lem_well_cartR_bd; auto.
    + rewrite Equal_Max in H9; apply (lem_well_cartR_bc c d a b) in H10; auto.
      destruct H10 as [H10 | [H10| H10]]; try rewrite H10; auto.
    + rewrite Equal_Max in H9, H10; apply lem_well_cartR_ac; auto.
    + rewrite Equal_Max in H9; apply (lem_well_cartR_bc c d a b) in H10; auto.
      destruct H10 as [H10 | [H10| H10]]; try rewrite H10; auto.
    + apply lem_well_cartR_bd; auto.
    + rewrite Equal_Max in H10; apply lem_well_cartR_bc; auto.
    + apply lem_well_cartR_bd; auto.
  - destruct H.
    assert ((En_y y) ⊂ R /\ (En_y y) ≠ Φ).
    { split.
      - unfold Subclass; intros; apply Axiom_Scheme in H1; destruct H1, H2, H2, H2.
        apply H in H2; apply Axiom_SchemeP in H2; destruct H2, H4; clear H2.
        apply Axiom_Scheme in H4; apply Axiom_Scheme in H5; destruct H4, H5.
        assert (Ordinal x /\ Ordinal x0); auto; apply ord_bel_eq in H7.
        rewrite H3; destruct H7 as [H7|[H7|H7]]; apply Property_Max in H7;
        auto; try (rewrite H7; unfold R; apply Axiom_Scheme; Ens).
        rewrite Equal_Max in H7; rewrite H7; apply Axiom_Scheme; Ens.
      - apply not_zero_exist_bel in H0; destruct H0; double H0; apply H in H1; PP H1 a b.
        apply Axiom_SchemeP in H2; clear H1; destruct H2, H2; clear H1.
        apply Axiom_Scheme in H2; apply Axiom_Scheme in H3.
        destruct H2, H3; apply not_zero_exist_bel.
        assert (Ordinal a /\ Ordinal b); auto; apply ord_bel_eq in H5.
        destruct H5 as [H5|[H5|H5]]; apply Property_Max in H5; auto.
        + exists b; apply Axiom_Scheme; split; auto; exists a, b; auto.
        + exists a; apply Axiom_Scheme; split; auto; exists a, b; split; auto.
          rewrite Equal_Max; symmetry; auto.
        + exists b; apply Axiom_Scheme; split; auto; exists a, b; auto. }
    clear H0; apply sub_noteq_firstmemb in H1; unfold FirstMember in H1; destruct H1.
    apply Axiom_Scheme in H0; destruct H0, H2 as [u [v H2]], H2.
    generalize (classic ((En_v (∩ En_y y) y) = Φ)); intros; destruct H4.
    + generalize (classic ((En_u (∩ En_y y) y) = Φ)); intros; destruct H5.
      * double H2; apply H in H6; unfold Cartesian in H6; apply Axiom_SchemeP in H6.
        destruct H6, H7; apply Axiom_Scheme in H7; apply Axiom_Scheme in H8; clear H6.
        destruct H7, H8; assert (Ordinal u /\ Ordinal v); auto.
        apply ord_bel_eq in H10; destruct H10 as [H10 | [H10 | H10]].
        { double H10; apply Property_Max in H11; auto.
          rewrite H11 in H3; rewrite H3 in *; clear H3 H11.
          assert (u ∈ (En_v v y)); try (apply Axiom_Scheme; Ens); rewrite H4 in H3.
          generalize (not_bel_zero u); intros; contradiction. }
        { double H10; apply Property_Max in H11; auto; rewrite Equal_Max in H11.
          rewrite H11 in H3; rewrite H3 in *; clear H3 H11.
          assert (v ∈ (En_u u y)); try (apply Axiom_Scheme; Ens); rewrite H5 in H3.
          generalize (not_bel_zero v); intros; contradiction. }
        { double H10; apply Property_Max in H11; rewrite H11 in H3.
          rewrite H3, H10 in *; clear H3 H6 H8 H9 H10; exists [v,v].
          unfold FirstMember; split; auto; intros; intro.
          apply lem_well_cartR_v with (y:= y) in H6; auto; clear H3 H11.
          destruct H6 as [a [b H6]], H6, H6, H8, H9, H10.
          assert (Ordinal a /\ Ordinal b); auto; apply ord_bel_eq in H12.
          destruct H12 as [H12 | [H12 | H12]].
          - apply Property_Max in H12; auto; rewrite H12 in H11.
            destruct H11 as [H11 | [H11 | H11]].
            + assert (b ∈ (En_y y)); try apply Axiom_Scheme; Ens.
              apply H1 in H13; elim H13; clear H12 H13; unfold Rrelation, E.
              apply Axiom_SchemeP; split; try apply ord_set; auto.
            + destruct H11; rewrite H11 in *; clear H9 H10 H11.
              assert (a ∈ (En_v v y)); try apply Axiom_Scheme; Ens.
              rewrite H4 in H9; generalize (not_bel_zero a); contradiction.
            + destruct H11, H13; rewrite H11 in H14.
              generalize (notin_fix v); intros; contradiction.
          - apply Property_Max in H12; auto; rewrite Equal_Max in H12.
            rewrite H12 in H11; destruct H11 as [H11 | [H11 | H11]].
            + assert (a ∈ (En_y y)); try apply Axiom_Scheme; Ens.
              apply H1 in H13; elim H13; clear H12 H13; unfold Rrelation, E.
              apply Axiom_SchemeP; split; try apply ord_set; auto.
            + destruct H11; rewrite H11 in H13.
              generalize (notin_fix v); intros; contradiction.
            + destruct H11; clear H11; destruct H13; rewrite H11 in *.
              clear H11 H12; assert (b ∈ (En_u v y)); try apply Axiom_Scheme; Ens.
              rewrite H5 in H11; generalize (not_bel_zero b); contradiction.
          - double H12; apply Property_Max in H13; auto; rewrite H13 in H11.
            rewrite H12 in *; clear H9 H10 H12; destruct H11 as [H9|[H9|H9]].
            + assert (b ∈ (En_y y)); try apply Axiom_Scheme; Ens.
              apply H1 in H10; elim H10; clear H13 H10; unfold Rrelation, E.
              apply Axiom_SchemeP; split; try apply ord_set; auto.
            + destruct H9; rewrite H9 in H10.
              generalize (notin_fix v); intros; contradiction.
            + destruct H9, H10; rewrite H9 in H11.
              generalize (notin_fix v); intros; contradiction. }
      * assert ((En_u (∩ En_y y) y) ⊂ R /\ (En_u (∩ En_y y) y) ≠ Φ).
        { split; auto; unfold Subclass; intros; apply Axiom_Scheme in H6.
          destruct H6, H7; apply H in H7; apply Axiom_SchemeP in H7; apply H7. }
        apply sub_noteq_firstmemb in H6; clear H5; destruct H6; apply Axiom_Scheme in H5.
        destruct H5, H7; exists [∩ (En_y y), ∩ (En_u (∩(En_y y)) y)].
        clear H5; double H7; apply H in H7; apply Axiom_SchemeP in H7.
        destruct H7; clear H7; destruct H9; apply Axiom_Scheme in H7.
        apply Axiom_Scheme in H9; clear H0; destruct H7, H9.
        double H8; apply Property_Max in H11; auto.
        unfold FirstMember; split; auto; intros; intro.
        apply lem_well_cartR_u with (y:= y) in H13; try rewrite Equal_Max; auto.
        clear H12; destruct H13 as [a [b H13]], H13, H13, H14, H15, H16.
        assert (Ordinal a /\ Ordinal b); auto; apply ord_bel_eq in H18.
        destruct H18 as [H18 | [H18 | H18]].
        { double H18; apply Property_Max in H19; auto; rewrite H19 in H17.
          destruct H17 as [H17 | [H17 | H17]].
          - assert (b ∈ (En_y y)); try apply Axiom_Scheme; Ens.
            apply H1 in H20; elim H20; clear H19 H20; unfold Rrelation, E.
            apply Axiom_SchemeP; split; try apply ord_set; auto.
          - destruct H17; rewrite H17 in *; clear H15 H16 H17.
            assert (a ∈ (En_v (∩ En_y y) y)); try apply Axiom_Scheme; Ens.
            rewrite H4 in H15; generalize (not_bel_zero a); contradiction.
          - destruct H17, H20; rewrite <- H17 in H20; rewrite H20 in H18.
            generalize (notin_fix b); intros; contradiction. }
        { double H18; apply Property_Max in H19; auto; rewrite Equal_Max in H19.
          rewrite H19 in H17; destruct H17 as [H17 | [H17 | H17]].
          - assert (a ∈ (En_y y)); try apply Axiom_Scheme; Ens.
            apply H1 in H20; elim H20; clear H19 H20; unfold Rrelation, E.
            apply Axiom_SchemeP; split; try apply ord_set; auto.
          - destruct H17; rewrite <- H17 in H20.
            generalize (notin_fix a); intros; contradiction.
          - destruct H17; clear H17; destruct H20; rewrite H17 in *.
            assert (b∈(En_u (∩ En_y y) y)); try apply Axiom_Scheme; Ens.
            apply H6 in H21. elim H21; unfold Rrelation, E.
            apply Axiom_SchemeP; split; try apply ord_set; auto. }
        { double H18; apply Property_Max in H19; rewrite H19 in H17.
          rewrite H18 in *; clear H15 H16 H18; destruct H17 as [H15|[H15|H15]].
          - assert (b ∈ (En_y y)); try apply Axiom_Scheme; Ens.
            apply H1 in H16; elim H16; clear H19 H16; unfold Rrelation, E.
            apply Axiom_SchemeP; split; try apply ord_set; auto.
          - destruct H15; rewrite <- H15 in H16.
            generalize (notin_fix b); intros; contradiction.
          - destruct H15; clear H15; destruct H16; rewrite H15 in H16.
            generalize (not_bel_and (∩ En_y y) (∩ En_u (∩ En_y y) y)); intros.
            destruct H17; split; auto. }
    + assert ((En_v (∩ En_y y) y) ⊂ R /\ (En_v (∩ En_y y) y) ≠ Φ).
      { split; auto; unfold Subclass; intros; apply Axiom_Scheme in H5.
        destruct H5, H6; apply H in H6; apply Axiom_SchemeP in H6; apply H6. }
      apply sub_noteq_firstmemb in H5; clear H4; destruct H5; apply Axiom_Scheme in H4.
      destruct H4, H6; exists [∩ (En_v (∩ En_y y) y), ∩ (En_y y)].
      clear H4; double H6; apply H in H6; apply Axiom_SchemeP in H6; destruct H6.
      clear H6; destruct H8; apply Axiom_Scheme in H6; apply Axiom_Scheme in H8.
      clear H0; destruct H6, H8; double H7; apply Property_Max in H10; auto.
      unfold FirstMember; split; auto; intros; intro.
      apply lem_well_cartR_v with (y:= y) in H12; auto; clear H11.
      destruct H12 as [a [b H12]], H12, H12, H13, H14, H15.
      assert (Ordinal a /\ Ordinal b); auto; apply ord_bel_eq in H17.
      destruct H17 as [H17 | [H17 | H17]].
      { double H17; apply Property_Max in H18; auto; rewrite H18 in H16.
        destruct H16 as [H16 | [H16 | H16]].
        - assert (b ∈ (En_y y)); try apply Axiom_Scheme; Ens.
          apply H1 in H19; elim H19; clear H18 H19; unfold Rrelation, E.
          apply Axiom_SchemeP; split; try apply ord_set; auto.
        - destruct H16; rewrite H16 in *; clear H14 H15 H16.
          assert (a ∈ (En_v (∩ En_y y) y)); try apply Axiom_Scheme; Ens.
          apply H5 in H14; destruct H14; unfold Rrelation, E.
          apply Axiom_SchemeP; split; try apply ord_set; auto.
        - destruct H16, H19; rewrite <- H16 in H20.
          generalize (notin_fix b); intros; contradiction. }
      { double H17; apply Property_Max in H18; auto; rewrite Equal_Max in H18.
        rewrite H18 in H16; destruct H16 as [H16 | [H16 | H16]].
        - assert (a ∈ (En_y y)); try apply Axiom_Scheme; Ens.
          apply H1 in H19; destruct H19; unfold Rrelation, E.
          apply Axiom_SchemeP; split; try apply ord_set; auto.
        - destruct H16; rewrite H16 in H19.
          generalize (not_bel_and (∩ En_y y) (∩ En_v (∩ En_y y) y)); intros.
          destruct H20; split; auto.
        - destruct H16, H19; rewrite <- H19, <- H16 in H7.
          generalize (notin_fix a); intros; contradiction. }
      { double H17; apply Property_Max in H18; rewrite H18 in H16.
        rewrite H17 in *; clear H14 H15 H17; destruct H16 as [H14|[H14|H14]].
        - assert (b ∈ (En_y y)); try apply Axiom_Scheme; Ens.
          apply H1 in H15; destruct H15; unfold Rrelation, E.
          apply Axiom_SchemeP; split; try apply ord_set; auto.
        - destruct H14; rewrite <- H14 in *.
          generalize (not_bel_and b (∩ En_v b y)); intros; destruct H16; auto.
        - destruct H14, H15; rewrite <- H15, <- H14 in H7.
          generalize (notin_fix b); intros; contradiction. }
Qed.

Hint Resolve well_order_cartR : set.


(* 178 Theorem  If [u,v] 《 [x,y], then [u,v] ∈ (max[x,y]+1) × (max[x,y]+1). *)

Theorem lele_bel_cart : forall u v x y,
  Rrelation ([u,v]) ≪ ([x,y]) ->
  [u,v] ∈ ((PlusOne (Max x y)) × (PlusOne (Max x y))).
Proof.
  intros.
  unfold Rrelation, LessLess in H; apply Axiom_Scheme in H.
  destruct H, H0, H0, H0, H0, H0, H1, H2; apply ord_set in H; destruct H.
  apply ord_eq in H2; auto; destruct H2; apply ord_set in H.
  apply ord_set in H4; destruct H, H4; apply ord_eq in H2; auto.
  apply ord_eq in H5; auto; destruct H2, H5; rewrite <- H2, <- H5 in *.
  rewrite <- H8, <- H9 in *; clear H H2 H4 H5 H6 H7 H8 H9 x0 x1 x2 x3.
  assert ((Max u v) ≼ (Max x y)).
  { unfold LessEqual; destruct H3 as [H3|[H3|H3]]; try tauto. }
  clear H3; unfold Cartesian in H0, H1; apply Axiom_SchemeP in H0.
  apply Axiom_SchemeP in H1; destruct H0, H1, H2, H3; unfold R in H2, H3, H4, H5.
  clear H0 H1; apply Axiom_Scheme in H2; apply Axiom_Scheme in H3; apply Axiom_Scheme in H4.
  apply Axiom_Scheme in H5; destruct H2, H3, H4, H5, H.
  - assert ((Max x y) ∈ R).
    { assert (Ordinal x /\ Ordinal y); auto; apply ord_bel_eq in H8.
      destruct H8 as[H8|[H8|H8]]; apply Property_Max in H8;auto;try rewrite H8.
      - unfold R; apply Axiom_Scheme; split; auto.
      - rewrite Equal_Max in H8; rewrite H8; unfold R; apply Axiom_Scheme; auto.
      - unfold R; apply Axiom_Scheme; split; auto. }
    double H8; apply ordnum_succ_ordnum in H9; unfold R in H8, H9; apply Axiom_Scheme in H8.
    apply Axiom_Scheme in H9; destruct H8, H9; unfold LessEqual in H.
    assert ((Max x y) ∈ (PlusOne (Max x y))).
    { unfold PlusOne; apply bel_union; right; apply Axiom_Scheme; split; auto. }
    unfold Ordinal, full in H11; destruct H11 as [_ H11]; apply H11 in H12.
    apply H12 in H; clear H8 H9 H10 H12; assert (Ordinal u /\ Ordinal v); auto.
    apply ord_bel_eq in H8; destruct H8 as [H8 | [H8 | H8]].
    + double H8; apply Property_Max in H9; auto; rewrite H9 in H; clear H9.
      double H; apply H11 in H9; apply H9 in H8; clear H9 H11; unfold Cartesian.
      apply Axiom_SchemeP; repeat split; try apply ord_set; auto.
    + double H8; apply Property_Max in H9; auto; rewrite Equal_Max in H9.
      rewrite H9 in H; clear H9; double H; apply H11 in H9; apply H9 in H8.
      clear H9 H11; unfold Cartesian; apply Axiom_SchemeP.
      repeat split; try apply ord_set; auto.
    + double H8; apply Property_Max in H9; auto; rewrite H9 in H; rewrite H8.
      clear H8 H9 H11; apply Axiom_SchemeP; repeat split; try apply ord_set; auto.
  - rewrite <- H in *; clear H; assert (Ordinal u /\ Ordinal v); auto.
    apply ord_bel_eq in H; destruct H as [H | [H | H]].
    + double H; apply Property_Max in H8; auto; rewrite H8; clear H8.
      unfold Cartesian; apply Axiom_SchemeP; repeat split; try apply ord_set; Ens.
      * apply bel_union; tauto.
      * apply bel_union; right; apply Axiom_Scheme; auto.
    + double H; apply Property_Max in H8; auto; rewrite Equal_Max in H8.
      rewrite H8; clear H8; unfold Cartesian; apply Axiom_SchemeP.
      repeat split; try apply ord_set; auto; try (apply bel_union; tauto).
      apply bel_union; right; apply Axiom_Scheme; auto.
    + double H; apply Property_Max in H8; rewrite H8; clear H8; rewrite H at 1.
      unfold Cartesian; apply Axiom_SchemeP; split; try apply ord_set; auto.
      split; apply bel_union; right; apply Axiom_Scheme; auto.
Qed.

Hint Resolve lele_bel_cart : set.


(* 179 Theorem  If x ∈ (C ~ W), then P(x × x) = x. *)

Definition En_Q u v x0 : Class :=
  \{\ λ a b, Rrelation ([a,b]) ≪ ([u,v]) /\ [a,b] ∈ x0 × x0 \}\.

Lemma card_eq_cart : forall x, Ensemble x -> P[x × x] = P[(P[x]) × (P[x])].
Proof.
  intros.
  double H; double H; apply Property_PClass in H0.
  apply card_equiv in H1; apply equiv_com in H1.
  unfold Equivalent in H1; destruct H1 as [f H1], H1, H2.
  assert (Ensemble (x × x) /\ Ensemble ((P[x]) × (P[x]))).
  { split; apply set_cart; Ens. }
  apply card_eq in H4; apply H4; clear H4.
  unfold Equivalent.
  exists \{\ λ a b, a ∈ (x × x) /\ b = [f[First a], f[Second a]] \}\.
  repeat split; unfold Relation; intros; try PP H4 c d; Ens.
  - destruct H4; apply Axiom_SchemeP in H4; apply Axiom_SchemeP in H5.
    destruct H4, H5, H6, H7; rewrite H8, H9; auto.
  - destruct H4; apply Axiom_SchemeP in H4; apply Axiom_SchemeP in H5.
    destruct H4, H5; apply Axiom_SchemeP in H6; apply Axiom_SchemeP in H7.
    destruct H6, H7, H8, H9; rewrite H11 in H10; clear H4 H5 H6 H7 H11.
    PP H8 a b; PP H9 c d; clear H8 H9; apply Axiom_SchemeP in H4; clear y z.
    apply Axiom_SchemeP in H5; destruct H4, H5, H6, H7; apply ord_set in H4.
    apply ord_set in H5; apply ordere_fst_snd in H4; apply ordere_fst_snd in H5.
    destruct H4, H5; rewrite H4, H5, H11, H12 in H10; clear H4 H5 H11 H12.
    rewrite <- H2 in H6, H7, H8, H9; destruct H1.
    apply Property_Value in H6; apply Property_Value in H7; auto.
    apply Property_Value in H8; apply Property_Value in H9; auto.
    double H7; double H9; apply Property_ran in H7; apply Property_ran in H11.
    AssE f[c]; AssE f[d]; apply ord_eq in H10; auto; clear H7 H11 H12 H13.
    destruct H10; rewrite H7 in H5; rewrite H10 in H9; clear H7 H10.
    assert ([f[a],a] ∈ f⁻¹ /\ [f[a],c] ∈ f⁻¹).
    { AssE [a,f[a]]; AssE [c,f[a]]; apply ord_set in H7; destruct H7.
      apply ord_set in H10; destruct H10 as [H10 _]; unfold Inverse.
      split; apply Axiom_SchemeP; split; try apply ord_set; auto. }
    assert ([f[b],b] ∈ f⁻¹ /\ [f[b],d] ∈ f⁻¹).
    { AssE [b,f[b]]; AssE [d,f[b]]; apply ord_set in H10; destruct H10.
      apply ord_set in H11; destruct H11 as [H11 _]; unfold Inverse.
      split; apply Axiom_SchemeP; split; try apply ord_set; auto. }
    apply H4 in H7; apply H4 in H10; rewrite H7, H10; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4, H5; apply Axiom_SchemeP in H5; apply H5.
    + apply Axiom_Scheme; split; Ens; PP H4 a b; exists [f[a],f[b]].
      double H5; apply Axiom_SchemeP in H6; rewrite <- H2 in H6; destruct H6, H7.
      destruct H1; apply Property_Value in H7; apply Property_Value in H8; Ens.
      apply Property_ran in H7; apply Property_ran in H8.
      apply Axiom_SchemeP; repeat split; try apply ord_set; try split; auto.
      * apply ord_set; Ens.
      * apply ord_set in H6; apply ordere_fst_snd in H6; destruct H6.
        rewrite H6, H10; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4, H5; apply Axiom_SchemeP in H5.
      destruct H5, H6; PP H6 a b; AssE [a,b]; apply ord_set in H9.
      apply ordere_fst_snd in H9; destruct H9; rewrite H9, H10 in H7; clear H9 H10.
      rewrite H7 in *; clear H5 H6 H7; apply Axiom_SchemeP in H8; destruct H8,H6.
      destruct H1; rewrite <- H2 in H6, H7; apply Property_Value in H6; auto.
      apply Property_Value in H7; auto; apply Property_ran in H6.
      apply Property_ran in H7; rewrite H3 in H6, H7; unfold Cartesian.
      apply Axiom_SchemeP; repeat split; auto.
    + apply Axiom_Scheme; split; Ens; PP H4 a b; clear H4; apply Axiom_SchemeP in H5.
      destruct H5, H5; rewrite <- H3 in H5, H6; unfold Range in H5, H6.
      apply Axiom_Scheme in H5; apply Axiom_Scheme in H6; destruct H5, H6, H7, H8.
      double H7; double H8; apply Property_dom in H9; apply Property_dom in H10.
      exists [x0,x1]; assert (Ensemble ([x0,x1])); try apply ord_set; Ens.
      apply Axiom_SchemeP; split; try apply ord_set; split; auto.
      * rewrite H2 in H9, H10; unfold Cartesian; apply Axiom_SchemeP.
        repeat split; try apply ord_set; Ens.
      * apply ord_set in H11; apply ordere_fst_snd in H11; destruct H1, H11.
        rewrite H11, H13; clear H11 H13; apply Property_Value in H9; auto.
        apply Property_Value in H10; auto; add ([x0, a] ∈ f) H9.
        add ([x1, b] ∈ f) H10; apply H1 in H9; apply H1 in H10.
        rewrite H9, H10; auto.
Qed.

Lemma equiv_cart_sing : forall x x0, Ensemble x0 -> x ≈ x × [x0].
Proof.
  intros.
  unfold Equivalent; exists (\{\ λ a b, a ∈ x /\ b = [a,x0] \}\).
  repeat split; intros; try (unfold Relation; intros; PP H0 a b; Ens).
  - destruct H0; apply Axiom_SchemeP in H0; apply Axiom_SchemeP in H1.
    destruct H0, H1, H2, H3; rewrite H4, H5; auto.
  - destruct H0; apply Axiom_SchemeP in H0; apply Axiom_SchemeP in H1.
    destruct H0, H1; apply Axiom_SchemeP in H2; apply Axiom_SchemeP in H3.
    destruct H2, H3, H4, H5; apply ord_set in H0; destruct H0.
    rewrite H6 in H7; apply ord_eq in H7; try apply H7; auto.
  - apply Axiom_Extent; split; intros.
    + unfold Domain in H0; apply Axiom_Scheme in H0; destruct H0, H1.
      apply Axiom_SchemeP in H1; apply H1.
    + unfold Domain; apply Axiom_Scheme; split; Ens; exists [z,x0].
      apply Axiom_SchemeP; repeat split; auto; apply ord_set; split; Ens.
      apply ord_set; split; Ens.
  - apply Axiom_Extent; split; intros.
    + unfold Range in H0; apply Axiom_Scheme in H0; destruct H0, H1.
      apply Axiom_SchemeP in H1; destruct H1, H2; rewrite H3 in *.
      unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
      unfold Singleton; apply Axiom_Scheme; split; Ens.
    + unfold Range; apply Axiom_Scheme; split; Ens; PP H0 a b.
      apply Axiom_SchemeP in H1; destruct H1, H2; exists a.
      apply Axiom_SchemeP; repeat split; auto; try apply ord_set; Ens.
      apply ord_set in H1; apply ord_eq; auto; split; auto.
      unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
      apply H4; apply bel_universe_set; Ens.
Qed.

Lemma lem_notint_card_cart_eq : forall f u v x0 ,
  Ensemble f[[u,v]] -> Ordinal f[[u, v]] -> x0 ∈ C ->
  P[f[[u, v]]] ∈ x0 -> f[[u, v]] ∈ x0.
Proof.
  intros; double H1.
  apply card_iff_eq in H1; destruct H1; unfold C in H3.
  apply Axiom_Scheme in H3; destruct H3 as [_ H3]; unfold Cardinal_Number in H3.
  destruct H3 as [H3 _]; apply Axiom_Scheme in H3; destruct H3 as [_ H3].
  assert (Ordinal f[[u, v]] /\ Ordinal x0); auto.
  apply ord_bel_eq in H5; destruct H5 as [H5 | [H5 | H5]]; auto.
  - unfold Ordinal in H0; destruct H0 as [_ H0]; apply H0 in H5.
    add (x0 ⊂ f [[u, v]]) H; apply card_le in H; clear H5.
    rewrite H4 in H; unfold LessEqual in H; destruct H.
    + generalize (not_bel_and x0 P[f[[u,v]]]); intros; destruct H5; auto.
    + rewrite <- H in H2; generalize (notin_fix x0); contradiction.
  - rewrite H5, H4 in H2; generalize (notin_fix x0); contradiction.
Qed.

Theorem notint_card_cart_eq : forall x, x ∈ (C ~ W) -> P[x × x] = x.
Proof.
  intros.
  generalize well_order_E; intros.
  unfold WellOrdered in H0; destruct H0; clear H0.
  generalize (classic (\{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \} = Φ)); intros.
  destruct H0.
  - generalize (classic (P[x × x] = x)); intros; destruct H2; auto.
    assert (x ∈ Φ). { rewrite <- H0; apply Axiom_Scheme; Ens. }
    generalize (not_bel_zero x); intros; contradiction.
  - assert (\{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \} ⊂ C /\
            \{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \} ≠ Φ).
    { split; auto; unfold Subclass; intros; apply Axiom_Scheme in H2.
      destruct H2, H3; apply bel_inter in H3; apply H3. }
    apply H1 in H2; clear H0 H1; destruct H2; unfold FirstMember in H0.
    destruct H0; apply Axiom_Scheme in H0; destruct H0, H2.
    generalize well_order_cartR, ord_not_set_R; intros; destruct H5.
    assert (Ensemble x0 /\ Ensemble x0); Ens; apply set_cart in H7.
    assert (x0 × x0 ⊂ R × R).
    { unfold Difference in H2; apply bel_inter in H2; destruct H2 as [H2 _].
      unfold C in H2; apply Axiom_Scheme in H2; destruct H2 as [_ H2].
      destruct H2 as [H2 _]; unfold Ordinal_Number in H2; unfold Ordinal in H5.
      destruct H5 as [_ H5]; apply H5 in H2; clear H5.
      unfold Cartesian, Subclass; intros; PP H5 a b; apply Axiom_SchemeP in H8.
      destruct H8, H9; apply H2 in H9; apply H2 in H10; apply Axiom_SchemeP; Ens. }
    apply lem_order_pre_sec_sub with (y:= x0 × x0) in H4; auto; clear H8.
    apply ord_well_order in H5; add (WellOrdered E R) H4; auto; clear H5.
    apply well_order_pre_set in H4; auto; clear H6 H7; destruct H4 as [f H4], H4, H5.
    unfold Order_PXY in H5; destruct H5, H7, H8; clear H4 H5 H7; double H8.
    apply order_pre_fun1_inv in H4; destruct H4 as [H4 _], H9.
    assert (forall u v, [u,v] ∈ (x0 × x0) -> f[[u,v]] ∈ x0).
    { intros.
      assert ((En_Q u v x0) ⊂ ((PlusOne (Max u v)) × (PlusOne (Max u v)))).
      { unfold Subclass; intros; PP H10 a b; apply Axiom_SchemeP in H11.
        destruct H11, H12; apply lele_bel_cart; auto. }
      assert (En_Q u v x0 ≈ f[[u, v]]).
      { rewrite <- H6 in H9; apply Property_Value in H9; try apply H4.
        apply Property_ran in H9; clear H10; unfold Equivalent.
        exists (f|(En_Q u v x0)); destruct H4; double H4; double H10.
        apply (fun_res_fun f (En_Q u v x0)) in H11; destruct H11, H13.
        apply (fun_res_fun f⁻¹ f[[u, v]]) in H12; destruct H12, H15.
        split; try split; auto; unfold Function, Relation.
        - split; intros; try PP H17 a b; Ens; unfold Inverse in H17.
          destruct H17; apply Axiom_SchemeP in H17; apply Axiom_SchemeP in H18.
          destruct H17, H18; unfold Restriction in H19, H20.
          apply bel_inter in H19; apply bel_inter in H20.
          destruct H19 as [H19 _], H20 as [H20 _].
          assert ([x1,z] ∈ f⁻¹ /\ [x1,y] ∈ f⁻¹).
          { unfold Inverse; split; apply Axiom_SchemeP; auto. }
          apply H10 in H21; symmetry; auto.
        - assert (En_Q u v x0 ⊂ dom(f)).
          { unfold Subclass, En_Q; intros; PP H17 a b; rewrite H6.
            apply Axiom_SchemeP in H18; apply H18. }
          apply inter_sub in H17; rewrite H17 in H13; auto.
        - apply Axiom_Extent; split; intros.
          + unfold Range in H17; apply Axiom_Scheme in H17; destruct H17, H18.
            unfold Restriction in H18; apply bel_inter in H18; destruct H18.
            unfold Cartesian in H19; apply Axiom_SchemeP in H19.
            destruct H19 as [_ H19], H19 as [H19 _]; PP H19 a b; clear H19.
            apply Axiom_SchemeP in H20; destruct H20, H20; rewrite <- H6 in H21.
            double H21; apply Property_Value in H22; auto.
            add ([[a, b], z] ∈ f) H22; clear H18 H19; apply H4 in H22.
            rewrite <- H22; clear H22; apply Property_Value' in H9; auto.
            apply Property_dom in H9; unfold Order_Pr in H5.
            assert ([a,b] ∈ dom( f) /\ [u,v] ∈ dom( f) /\ 
            Rrelation ([a,b]) ≪ ([u,v])); auto.
            apply H5 in H18; unfold Rrelation, E in H18.
            apply Axiom_SchemeP in H18; apply H18.
          + unfold Range; apply Axiom_Scheme; split; Ens; double H8; double H9.
            apply sec_R_ord in H18; destruct H18 as [_ H18].
            apply H18 in H19; double H17; apply H19 in H20; clear H19 H18.
            double H20; apply Axiom_Scheme in H19; destruct H19, H20; exists x1.
            unfold Restriction; apply bel_inter; split; auto.
            unfold Cartesian; apply Axiom_SchemeP; split; Ens.
            split; try apply bel_universe_set; Ens; clear H H1 H2 H3 H13 H14 H15 H16.
            apply order_pre_fun1_inv in H5; destruct H5 as [_ H5].
            unfold Order_Pr in H5; rewrite <- dom_ran_inv' in H5.
            assert (z∈ran(f) /\ f[[u,v]]∈ran(f) /\ Rrelation z E f[[u,v]]).
            { repeat split; auto; unfold Rrelation, E; apply Axiom_SchemeP.
              split; auto; apply ord_set; Ens. }
            apply H5 in H; pattern f at 3 in H.
            rewrite <- rel_inv_fix in H; try apply H4.
            apply Property_Value' in H9; auto; apply Property_dom in H9.
            rewrite dom_ran_inv in H9; double H20; apply Property_ran in H2.
            rewrite<-dom_ran_inv''' in H; try rewrite rel_inv_fix; try apply H4;auto.
            rewrite dom_ran_inv' in H2; apply Property_Value in H2; auto.
            assert ([z,x1] ∈ f ⁻¹).
            { apply Axiom_SchemeP; split; auto; apply ord_set.
              AssE [x1,z]; apply ord_set in H3; destruct H3; auto. }
            add ([z,x1] ∈ f ⁻¹) H2; apply H10 in H2; rewrite H2 in H.
            apply Property_dom in H1; rewrite H6 in H1; clear H2 H3.
            PP H1 a b; unfold En_Q; apply Axiom_SchemeP; repeat split; Ens. }
      assert ([u,v] ∈ (W × W) -> f[[u,v]] ∈ x0).
      { clear H9; intros; clear H x.
        assert (W × W ⊂ x0 × x0).
        { unfold Subclass; intros; PP H a b; apply Axiom_SchemeP in H12.
          destruct H12, H13; double H13; double H14; unfold W in H15, H16.
          apply Axiom_Scheme in H15; apply Axiom_Scheme in H16; destruct H15 as [_ H15].
          destruct H16 as [_ H16], H15 as [H15 _], H16 as [H16 _].
          apply Axiom_SchemeP; split; auto; apply bel_inter in H2; destruct H2.
          unfold C in H2; apply Axiom_Scheme in H2; destruct H2 as [_ H2].
          unfold Cardinal_Number, Ordinal_Number in H2; destruct H2 as [H2 _].
          apply Axiom_Scheme in H2; destruct H2 as [_ H2]; apply Axiom_Scheme in H17.
          destruct H17 as [_ H17]; add (Ordinal x0) H15; add (Ordinal x0) H16.
          apply ord_bel_eq in H15; apply ord_bel_eq in H16.
          destruct H15 as [H15|[H15|H15]], H16 as [H16|[H16|H16]]; auto.
          - destruct H17; apply Axiom_Scheme; split; Ens.
            apply (int_bel_int b _); auto; apply Axiom_Scheme in H14; apply H14.
          - rewrite H16 in H14; contradiction.
          - destruct H17; apply Axiom_Scheme; split; Ens.
            apply (int_bel_int a _); auto; apply Axiom_Scheme in H13; apply H13.
          - destruct H17; apply Axiom_Scheme; split; Ens.
            apply (int_bel_int b _); auto; apply Axiom_Scheme in H14; apply H14.
          - rewrite H16 in H14; contradiction.
          - rewrite H15 in H13; contradiction.
          - rewrite H15 in H13; contradiction.
          - rewrite H15 in H13; contradiction. }
      double H9; apply H in H9; rewrite <- H6 in H9.
      apply Axiom_SchemeP in H12; destruct H12, H13.
      assert (PlusOne (Max u v) ∈ W).
      { apply int_succ; double H13; double H14; unfold W in H15, H16.
        apply Axiom_Scheme in H15; apply Axiom_Scheme in H16; destruct H15 as [_ H15].
        destruct H16 as [_ H16], H15 as [H15 _], H16 as [H16 _].
        assert (Ordinal u /\ Ordinal v); auto; apply ord_bel_eq in H17.
        destruct H17 as [H17|[H17|H17]]; try apply Property_Max in H17; auto.
        - rewrite H17; auto.
        - rewrite Equal_Max in H17; rewrite H17; auto.
        - rewrite H17; auto. }
      assert (Finite (PlusOne (Max u v)) /\ Finite (PlusOne (Max u v))).
      { double H15; generalize W_sub_C; intros; apply H17 in H16.
        clear H17; apply card_iff_eq in H16; destruct H16 as [_ H16].
        unfold Finite; rewrite H16; auto. }
      apply fin_cart in H16; unfold Finite in H16.
      assert (Ensemble ((PlusOne (Max u v)) × (PlusOne (Max u v))) /\
      ((En_Q u v x0) ⊂ (PlusOne (Max u v)) × (PlusOne (Max u v)))).
      { split; auto; apply set_cart; Ens. }
      clear H10 H15; elim H17; intros; apply card_le in H17.
      assert (P[En_Q u v x0] = P[f[[u, v]]]).
      { apply sub_set in H15; auto; clear H10 H12 H13 H14 H16 H17.
        apply Property_Value in H9; try apply H4; apply Property_ran in H9.
        apply card_eq; Ens. }
      rewrite H18 in H17; clear H11 H10 H15 H18.
      apply Property_Value in H9; try apply H4; apply Property_ran in H9.
      clear H12 H13 H14; apply H8 in H9; unfold R in H9; apply Axiom_Scheme in H9.
      destruct H9; apply bel_inter in H2; double H2; destruct H11 as [H11 _].
      apply Axiom_Scheme in H11; destruct H11 as [_ H11], H11 as [H11 _].
      apply Axiom_Scheme in H11; destruct H11 as [_ H11].
      assert (W ⊂ x0).
      { unfold Subclass; intros; unfold W in H12; apply Axiom_Scheme in H12.
        destruct H12; double H13; destruct H14 as [H14 _], H2.
        apply Axiom_Scheme in H15; destruct H15 as [_ H15].
        add (Ordinal x0) H14; apply ord_bel_eq in H14.
        destruct H14 as [H14 | [H14 | H14]]; auto.
        - destruct H15; apply Axiom_Scheme; split; Ens.
          apply (int_bel_int z _); auto.
        - destruct H15; rewrite <- H14; apply Axiom_Scheme; Ens. }
      apply H12 in H16; clear H12.
      assert (P[f[[u, v]]] ∈ x0).
      { unfold LessEqual in H17; destruct H17; try rewrite H12; auto.
        destruct H11 as [_ H11]; apply H11 in H16; apply H16 in H12; auto. }
      apply lem_notint_card_cart_eq in H12; destruct H2; auto. }
      intros; generalize (classic (x0 = W)); intros; destruct H13.
      - rewrite H13 in H9; apply H12; auto.
      - double H9; rewrite <- H6 in H9.
        unfold Cartesian in H14; apply Axiom_SchemeP in H14; destruct H14, H15.
        clear H x; unfold Difference in H2; apply bel_inter in H2.
        destruct H2 as [H2 _]; double H2; unfold C in H2; apply Axiom_Scheme in H2.
        destruct H2 as [_ H2]; unfold Cardinal_Number, Ordinal_Number in H2.
        destruct H2 as [H2 _]; apply Axiom_Scheme in H2; destruct H2 as [_ H2].
        clear H0; double H2; double H2; add (u ∈ x0) H2; add (v ∈ x0) H17.
        apply ord_bel_ord in H2; apply ord_bel_ord in H17.
        assert (Ordinal u /\ Ordinal v); auto.
        apply ord_bel_eq in H18; generalize (classic (Max u v ∈ W)); intros.
        destruct H18 as [H18 | [H18 | H18]]; double H18.
        + apply Property_Max in H20; auto; rewrite H20 in *.
          clear H20; destruct H19.
          * apply H12; apply Axiom_SchemeP; repeat split; auto.
            apply Axiom_Scheme in H19; destruct H19; apply Axiom_Scheme; split; Ens.
            apply int_bel_int in H18; auto.
          * assert (v ∈ (R ~ W)).
            { unfold Difference; apply bel_inter; split; apply Axiom_Scheme; Ens. }
            apply notint_card_plus_eq in H20; clear H6 H7 H12 H14; destruct H4 as[H4 _].
            apply Property_Value in H9;auto; apply Property_ran in H9.
            apply H8 in H9; clear H8; assert (v ∈ R). apply Axiom_Scheme; Ens.
            apply ordnum_succ_ordnum in H6; AssE (PlusOne v); clear H6.
            assert(Ensemble((PlusOne v)×(PlusOne v)));try apply set_cart;Ens.
            double H10; apply sub_set in H8; auto.
            add (En_Q u v x0 ⊂ (PlusOne v) × (PlusOne v)) H6; clear H10.
            apply card_le in H6; apply card_eq in H11; Ens.
            rewrite H11 in H6; clear H8 H11; double H7; apply card_eq_cart in H7.
            rewrite H7 in H6; clear H7; double H.
            apply card_iff_eq in H7; destruct H7 as [_ H7].
            assert (P[v] ≺ P[x0]).
            { assert (Ordinal v /\ Ordinal x0); auto; apply ord_sub_iff_le in H10.
              assert (v ≼ x0); unfold LessEqual; try tauto; apply H10 in H11.
              assert (Ensemble x0 /\ v ⊂ x0); Ens; apply card_le in H12.
              clear H10 H11; unfold LessEqual in H12; destruct H12; auto.
              apply card_eq in H10; Ens; apply equiv_com in H10.
              unfold C in H; apply Axiom_Scheme in H; destruct H.
              apply H11 in H16; try contradiction; apply Axiom_Scheme; Ens. }
            assert (P[(P[PlusOne v]) × (P[PlusOne v])] = P[PlusOne v]).
            { apply Property_PClass in H8.
              generalize (classic (P[(P[PlusOne v]) × (P[PlusOne v])] =
              P[PlusOne v])); intros; destruct H11; auto.
              assert (P[PlusOne v] ∈ \{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \}).
              { apply Axiom_Scheme; repeat split; Ens.
                unfold Difference; apply bel_inter; split; auto.
                apply Axiom_Scheme; split; Ens; intro; symmetry in H20.
                assert (v ∈ (PlusOne v)).
                { unfold PlusOne; apply bel_union; right; unfold Singleton.
                  apply Axiom_Scheme; split; Ens. }
                apply fin_card_eq in H20; auto.
                - rewrite H20 in H14; generalize (notin_fix v); contradiction.
                - assert (v ≼ (PlusOne v)); unfold LessEqual; auto.
                  apply ord_sub_iff_le in H21; auto; clear H22; split; auto.
                  assert (v ∈ R). apply Axiom_Scheme; Ens.
                  apply ordnum_succ_ordnum in H22; apply Axiom_Scheme in H22; apply H22. }
              apply H1 in H12; destruct H12; unfold Rrelation, E.
              apply Axiom_SchemeP; split; try apply ord_set; Ens.
              rewrite H20, <- H7; auto. }
            rewrite H11, H20 in H6; clear H11 H20; rewrite H7 in H10.
            assert (P[f[[u, v]]] ∈ x0).
            { unfold LessEqual in H6; destruct H6; try rewrite H6; auto.
              destruct H0; apply H11 in H10; apply H10 in H6; auto. }
            unfold R in H9; apply Axiom_Scheme in H9; destruct H9.
            apply lem_notint_card_cart_eq in H11; auto.
        + apply Property_Max in H20; auto; rewrite Equal_Max in H20.
          rewrite H20 in *; clear H20; destruct H19.
          * apply H12; apply Axiom_SchemeP; repeat split; auto.
            apply Axiom_Scheme in H19; destruct H19; apply Axiom_Scheme; split; Ens.
            apply int_bel_int in H18; auto.
          * assert (u ∈ (R ~ W)).
            { unfold Difference; apply bel_inter; split; apply Axiom_Scheme; Ens. }
            apply notint_card_plus_eq in H20; clear H6 H7 H12 H14; destruct H4 as[H4 _].
            apply Property_Value in H9;auto; apply Property_ran in H9.
            apply H8 in H9; clear H8; assert (u ∈ R). apply Axiom_Scheme; Ens.
            apply ordnum_succ_ordnum in H6; AssE (PlusOne u); clear H6.
            assert(Ensemble((PlusOne u)×(PlusOne u)));try apply set_cart;Ens.
            double H10; apply sub_set in H8; auto.
            add (En_Q u v x0 ⊂ (PlusOne u) × (PlusOne u)) H6; clear H10.
            apply card_le in H6; apply card_eq in H11; Ens.
            rewrite H11 in H6; clear H8 H11; double H7; apply card_eq_cart in H7.
            rewrite H7 in H6; clear H7; double H.
            apply card_iff_eq in H7; destruct H7 as [_ H7].
            assert (P[u] ≺ P[x0]).
            { assert (Ordinal u /\ Ordinal x0); auto; apply ord_sub_iff_le in H10.
              assert (u ≼ x0); unfold LessEqual; try tauto; apply H10 in H11.
              assert (Ensemble x0 /\ u ⊂ x0); Ens; apply card_le in H12.
              clear H10 H11; unfold LessEqual in H12; destruct H12; auto.
              apply card_eq in H10; Ens; apply equiv_com in H10.
              unfold C in H; apply Axiom_Scheme in H; destruct H.
              apply H11 in H15; try contradiction; apply Axiom_Scheme; Ens. }
            assert (P[(P[PlusOne u]) × (P[PlusOne u])] = P[PlusOne u]).
            { apply Property_PClass in H8.
              generalize (classic (P[(P[PlusOne u]) × (P[PlusOne u])] =
              P[PlusOne u])); intros; destruct H11; auto.
              assert (P[PlusOne u] ∈ \{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \}).
              { apply Axiom_Scheme; repeat split; Ens.
                unfold Difference; apply bel_inter; split; auto.
                apply Axiom_Scheme; split; Ens; intro; symmetry in H20.
                assert (u ∈ (PlusOne u)).
                { unfold PlusOne; apply bel_union; right; unfold Singleton.
                  apply Axiom_Scheme; split; Ens. }
                apply fin_card_eq in H20; auto.
                - rewrite H20 in H14; generalize (notin_fix u); contradiction.
                - assert (u ≼ (PlusOne u)); unfold LessEqual; auto.
                  apply ord_sub_iff_le in H21; auto; clear H22; split; auto.
                  assert (u ∈ R). apply Axiom_Scheme; Ens.
                  apply ordnum_succ_ordnum in H22; apply Axiom_Scheme in H22; apply H22. }
              apply H1 in H12; destruct H12; unfold Rrelation, E.
              apply Axiom_SchemeP; split; try apply ord_set; Ens.
              rewrite H20, <- H7; auto. }
            rewrite H11, H20 in H6; clear H11 H20; rewrite H7 in H10.
            assert (P[f[[u, v]]] ∈ x0).
            { unfold LessEqual in H6; destruct H6; try rewrite H6; auto.
              destruct H0; apply H11 in H10; apply H10 in H6; auto. }
            unfold R in H9; apply Axiom_Scheme in H9; destruct H9.
            apply lem_notint_card_cart_eq in H11; auto.
        + apply Property_Max in H20; auto; rewrite H18, H20 in *.
          clear H16 H18 H20; destruct H19.
          * apply H12; apply Axiom_SchemeP; repeat split; auto.
          * assert (v ∈ (R ~ W)).
            { unfold Difference; apply bel_inter; split; apply Axiom_Scheme; Ens. }
            apply notint_card_plus_eq in H18; clear H6 H7 H12 H14; destruct H4 as[H4 _].
            apply Property_Value in H9; auto; apply Property_ran in H9.
            apply H8 in H9; clear H8; assert (v ∈ R). apply Axiom_Scheme; Ens.
            apply ordnum_succ_ordnum in H6; AssE (PlusOne v); clear H6.
            assert(Ensemble((PlusOne v)×(PlusOne v)));try apply set_cart;Ens.
            double H10; apply sub_set in H8; auto.
            add (En_Q v v x0 ⊂ (PlusOne v) × (PlusOne v)) H6; clear H10.
            apply card_le in H6; apply card_eq in H11; Ens.
            rewrite H11 in H6; clear H8 H11; double H7; apply card_eq_cart in H7.
            rewrite H7 in H6; clear H7; double H.
            apply card_iff_eq in H7; destruct H7 as [_ H7].
            assert (P[v] ≺ P[x0]).
            { assert (Ordinal v /\ Ordinal x0); auto; apply ord_sub_iff_le in H10.
              assert (v ≼ x0); unfold LessEqual; try tauto; apply H10 in H11.
              assert (Ensemble x0 /\ v ⊂ x0); Ens; apply card_le in H12.
              clear H10 H11; unfold LessEqual in H12; destruct H12; auto.
              apply card_eq in H10; Ens; apply equiv_com in H10.
              unfold C in H; apply Axiom_Scheme in H; destruct H.
              apply H11 in H15; try contradiction; apply Axiom_Scheme; Ens. }
            assert (P[(P[PlusOne v]) × (P[PlusOne v])] = P[PlusOne v]).
            { apply Property_PClass in H8.
              generalize (classic (P[(P[PlusOne v]) × (P[PlusOne v])] =
              P[PlusOne v])); intros; destruct H11; auto.
              assert (P[PlusOne v] ∈ \{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \}).
              { apply Axiom_Scheme; repeat split; Ens.
                unfold Difference; apply bel_inter; split; auto.
                apply Axiom_Scheme; split; Ens; intro; symmetry in H18.
                assert (v ∈ (PlusOne v)).
                { unfold PlusOne; apply bel_union; right; unfold Singleton.
                  apply Axiom_Scheme; split; Ens. }
                apply fin_card_eq in H18; auto.
                - rewrite H18 in H14; generalize (notin_fix v); contradiction.
                - assert (v ≼ (PlusOne v)); unfold LessEqual; auto.
                  apply ord_sub_iff_le in H19; auto; clear H20; split; auto.
                  assert (v ∈ R). apply Axiom_Scheme; Ens.
                  apply ordnum_succ_ordnum in H20; apply Axiom_Scheme in H20; apply H20. }
              apply H1 in H12; destruct H12; unfold Rrelation, E.
              apply Axiom_SchemeP; split; try apply ord_set; Ens.
              rewrite H18, <- H7; auto. }
            rewrite H11, H18 in H6; clear H11 H18; rewrite H7 in H10.
            assert (P[f[[v, v]]] ∈ x0).
            { unfold LessEqual in H6; destruct H6; try rewrite H6; auto.
              destruct H0; apply H11 in H10; apply H10 in H6; auto. }
            unfold R in H9; apply Axiom_Scheme in H9; destruct H9.
            apply lem_notint_card_cart_eq in H11; auto. }
    assert (P[x0 × x0] ≼ x0).
    { assert (P[dom(f)] = P[ran(f)]).
      { apply card_eq; unfold Equivalent; Ens.
        assert (Ensemble x0 /\ Ensemble x0); auto.
        apply set_cart in H10; rewrite <- H6 in H10; split; auto.
        apply Axiom_Substitution; auto; apply H4. }
      assert (ran(f) ⊂ x0).
      { unfold Subclass; intros; unfold Range in H11; apply Axiom_Scheme in H11.
        destruct H11, H12; double H12; apply Property_dom in H13; double H13.
        apply Property_Value in H13; try apply H4; add ([x1, f[x1]] ∈ f) H12.
        apply H4 in H12; rewrite H12; clear H12 H13; rewrite H6 in H14.
        PP H14 a b; apply H9 in H12; auto. }
      add (ran( f) ⊂ x0) H0; apply card_le in H0; unfold Difference in H2.
      clear H11; apply bel_inter in H2; destruct H2 as [H2 _].
      apply card_iff_eq in H2; destruct H2 as [_ H2]; rewrite H2 in H0.
      rewrite <- H6, H10; auto. }
    unfold LessEqual in H10; destruct H10; try contradiction.
    assert (P[x0] ≼ P[x0 × x0]).
    { unfold Difference in H2; apply bel_inter in H2; destruct H2.
      unfold Complement in H11; apply Axiom_Scheme in H11; destruct H11 as [_ H11].
      generalize (classic (x0 = Φ)); intros; destruct H12.
      - rewrite H12 in H11; generalize (zero_not_int x); intros.
        destruct H13 as [H13 _]; contradiction.
      - apply not_zero_exist_bel in H12; destruct H12 as [z H12].
        assert (P[x0] = P[x0 × [z]]).
        { apply card_eq; try split; auto; try apply equiv_cart_sing; Ens.
          apply set_cart; split; try apply sing_set; Ens. }
        rewrite H13; apply card_le; split; try apply set_cart; auto.
        unfold Subclass; intros; PP H14 a b; apply Axiom_SchemeP in H15.
        destruct H15, H16; unfold Singleton in H17; apply Axiom_Scheme in H17.
        destruct H17; apply Axiom_SchemeP; repeat split; auto.
        rewrite H18; try apply bel_universe_set; Ens. }
    unfold LessEqual in H11; apply bel_inter in H2; destruct H2 as [H2 _].
    double H2; apply card_iff_eq in H2; destruct H2 as [_ H2], H11.
    + unfold C in H12; apply Axiom_Scheme in H12; destruct H12 as [_ H12].
      unfold Cardinal_Number, Ordinal_Number in H12; destruct H12 as [H12 _].
      apply Axiom_Scheme in H12; destruct H12 as [_ H12], H12 as [_ H12].
      unfold full in H12; apply H12 in H10; apply H10 in H11.
      rewrite H2 in H11; generalize (notin_fix x0); intros; contradiction.
    + rewrite <- H11, H2 in H10; generalize (notin_fix x0); contradiction.
Qed.

Hint Resolve notint_card_cart_eq : set.


(* 180 Theorem  If x and y are non-empty members of C, one of which fails to
   belong to W, then P[x×y] = max[P[x],P[y]]. *)

Theorem Theorem180_Not :
  exists x y, x ∈ C /\ y ∈ C /\ x ∉ W /\ P[x × y] <> Max P[x] P[y].
Proof.
  exists W, Φ; generalize (zero_not_int Φ); intros.
  destruct H as [H _]; double H; apply W_sub_C in H0.
  repeat split; try apply W_bel_C; try apply notin_fix; auto.
  generalize W_bel_C; intros; apply card_iff_eq in H0.
  apply card_iff_eq in H1; destruct H0 as [_ H0], H1 as [_ H1].
  assert (W × Φ = Φ).
  { apply Axiom_Extent; split; intros.
    - PP H2 a b; apply Axiom_SchemeP in H3; destruct H3, H4.
      generalize (not_bel_zero b); intros; contradiction.
    - generalize (not_bel_zero z); intros; contradiction. }
  rewrite H2, H0, H1; clear H0 H1 H2; double H; unfold W in H0.
  apply Axiom_Scheme in H0; destruct H0 as [_ H0], H0 as [H0 _].
  generalize Property_W; intros; double H.
  apply Property_Max in H2; auto; rewrite Equal_Max in H2; rewrite H2.
  intro; rewrite H3 in H; generalize (notin_fix W); contradiction.
Qed.

Lemma Lemma180 : forall x y, x × y ≈ y × x.
Proof.
  intros.
  unfold Equivalent; exists \{\ λ a b, a ∈ (x × y) /\ b ∈ [a]⁻¹ \}\.
  repeat split; intros; try (unfold Relation; intros; PP H a b; Ens).
  - destruct H; apply Axiom_SchemeP in H; apply Axiom_SchemeP in H0.
    destruct H, H0, H1, H2; unfold Singleton in H3, H4.
    PP H3 a b; PP H4 c d; clear H1 H2 H3 H4; apply Axiom_SchemeP in H5.
    apply Axiom_SchemeP in H6; destruct H5, H6; apply Axiom_Scheme in H2.
    apply Axiom_Scheme in H4; destruct H2, H4; clear H1 H2 H3 H4.
    apply ord_set in H; apply ord_set in H0; destruct H.
    destruct H0 as [_ H0]; assert (x0 ∈ μ); try apply bel_universe_set; Ens.
    double H2; apply H5 in H2; apply H6 in H3; clear H5 H6.
    rewrite <- H3 in H2; clear H3; apply ord_set in H1; destruct H1.
    apply ord_eq in H2; auto; destruct H2; rewrite H2, H4; auto.
  - destruct H; apply Axiom_SchemeP in H; apply Axiom_SchemeP in H0.
    destruct H, H0; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1, H2; clear H H0 H1 H2; destruct H3, H4.
    PP H0 a b; PP H2 c d; apply Axiom_SchemeP in H3; apply Axiom_SchemeP in H4.
    destruct H3, H4; apply Axiom_Scheme in H5; apply Axiom_Scheme in H6.
    destruct H5, H6; rewrite H7 in H8; try apply bel_universe_set; Ens.
    apply H8; apply bel_universe_set; Ens.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H; destruct H, H0.
      apply Axiom_SchemeP in H0; apply H0.
    + apply Axiom_Scheme; split; Ens; PP H a b; exists [b,a].
      apply Axiom_SchemeP; assert (Ensemble ([a,b])); Ens.
      apply ord_set in H1; destruct H1.
      split; try (apply ord_set; split; apply ord_set; Ens).
      split; auto; unfold Inverse; apply Axiom_SchemeP.
      split; try apply ord_set; auto; unfold Singleton.
      apply Axiom_Scheme; split; try apply ord_set; Ens.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H; destruct H, H0.
      apply Axiom_SchemeP in H0; destruct H0, H1; PP H1 a b; clear H1.
      apply Axiom_SchemeP in H3; destruct H3, H3; unfold Inverse in H2.
      PP H2 c d; clear H2; apply Axiom_SchemeP in H5; destruct H5.
      clear H0 H2; unfold Singleton in H5; apply Axiom_Scheme in H5.
      destruct H5; apply ord_set in H0.
      assert ([a, b] ∈ μ); try apply bel_universe_set; Ens; apply H2 in H5.
      apply ord_eq in H5; auto; clear H0 H2; destruct H5.
      rewrite H0, H2; unfold Cartesian; apply Axiom_SchemeP.
      repeat split; try apply ord_set; Ens.
    + unfold Range; apply Axiom_Scheme; split; Ens; PP H a b.
      apply Axiom_SchemeP in H0; destruct H0, H1; double H0; exists [b,a].
      apply ord_set in H3; destruct H3; apply Axiom_SchemeP.
      repeat split; try (apply ord_set; split; apply ord_set; Ens).
      * unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
        apply ord_set; split; auto.
      * unfold Inverse, Singleton; apply Axiom_SchemeP; split; auto.
        apply Axiom_Scheme; split; try apply ord_set; Ens.
Qed.

Lemma Lemma180' : forall x y,
  x ∈ C -> y ∈ C -> x ∉ W -> x ≠ Φ -> y ≠ Φ -> P[x × y] = Max P[x] P[y].
Proof.
  intros.
  assert (x ∈ (C ~ W)).
  { unfold Difference; apply bel_inter; split; auto.
    unfold Complement; apply Axiom_Scheme; split; Ens. }
  apply notint_card_cart_eq in H4; double H; double H0; unfold C in H5, H6.
  apply Axiom_Scheme in H5; apply Axiom_Scheme in H6; destruct H5, H6.
  unfold Cardinal_Number, Ordinal_Number in H7, H8; destruct H7, H8.
  clear H5 H6 H9 H10; apply Axiom_Scheme in H7; apply Axiom_Scheme in H8.
  destruct H7, H8; assert (Ordinal x /\ Ordinal y); auto.
  apply ord_bel_eq in H9; destruct H9 as [H9 | [H9 | H9]].
  - assert (Ensemble (y × y) /\ (x × y) ⊂ (y × y)).
    { split; unfold Subclass; intros.
      - apply set_cart; split; auto.
      - unfold Ordinal, full in H8; destruct H8 as [_ H8]; apply H8 in H9.
        PP H10 a b; clear H10; apply Axiom_SchemeP in H11; unfold Cartesian.
        apply Axiom_SchemeP; destruct H11, H11; repeat split; auto. }
    apply card_le in H10; apply not_zero_exist_bel in H2; destruct H2.
    assert (y ≈ ([x0] × y)).
    { apply equiv_tran with (y:= y × [x0]); try apply equiv_cart_sing; Ens.
      apply Lemma180. }
    assert (Ensemble (x × y) /\ ([x0] × y) ⊂ (x × y)).
    { split; try apply set_cart; Ens; unfold Subclass; intros.
      PP H12 a b; apply Axiom_SchemeP in H13; destruct H13, H14.
      apply Axiom_SchemeP; repeat split; auto; unfold Singleton in H14.
      apply Axiom_Scheme in H14; destruct H14; rewrite H16; auto.
      apply bel_universe_set; Ens. }
    assert (Ensemble y /\ Ensemble ([x0] × y)).
    { split; auto; apply set_cart; split; auto; apply sing_set; Ens. }
    apply card_le in H12; apply card_eq in H13; apply H13 in H11.
    rewrite <- H11 in H12; clear H11 H13.
    assert (y ∈ (C ~ W)).
    { unfold Difference; apply Axiom_Scheme; repeat split; auto.
      unfold Complement; apply Axiom_Scheme; split; auto; intro.
      unfold W in H11; apply Axiom_Scheme in H11; destruct H11 as [_ H11].
      apply int_bel_int in H9; auto; destruct H1; unfold W.
      apply Axiom_Scheme; split; auto. }
    apply notint_card_cart_eq in H11; rewrite H11 in H10; clear H5 H7 H11.
    apply card_iff_eq in H; apply card_iff_eq in H0; destruct H, H0.
    rewrite H5, H7 in *; apply Property_Max in H9; auto; rewrite H9.
    apply le_tran_eq; auto.
  - assert (Ensemble (x × x) /\ (x × y) ⊂ (x × x)).
    { split; unfold Subclass; intros; try (apply set_cart; Ens).
      unfold Ordinal, full in H6; destruct H6 as [_ H6]; apply H6 in H9.
      PP H10 a b; clear H10; apply Axiom_SchemeP in H11; unfold Cartesian.
      apply Axiom_SchemeP; destruct H11, H11; repeat split; auto. }
    apply card_le in H10; rewrite H4 in H10; clear H4.
    apply not_zero_exist_bel in H3; destruct H3.
    assert (x ≈ (x × [x0])); try apply equiv_cart_sing; Ens.
    assert (Ensemble (x × y) /\ (x × [x0]) ⊂ (x × y)).
    { split; try apply set_cart; Ens; unfold Subclass; intros.
      PP H11 a b; apply Axiom_SchemeP in H12; destruct H12, H13.
      apply Axiom_SchemeP; repeat split; auto; unfold Singleton in H13.
      apply Axiom_Scheme in H14; destruct H14; rewrite H15; auto.
      apply bel_universe_set; Ens. }
    assert (Ensemble x /\ Ensemble (x × [x0])).
    { split; auto; apply set_cart; split; auto; apply sing_set; Ens. }
    apply card_le in H11; apply card_eq in H12; apply H12 in H4.
    rewrite <- H4 in H11; clear H4 H5 H7 H12; apply card_iff_eq in H.
    apply card_iff_eq in H0; destruct H, H0; rewrite H4, H5 in *.
    apply Property_Max in H9; auto; rewrite Equal_Max in H9.
    rewrite H9; apply le_tran_eq; auto.
  - rewrite <- H9 in *; clear H0 H1 H2 H3 H5 H6 H7 H8 H9.
    apply card_iff_eq in H; destruct H; rewrite H0; assert (x=x); auto.
    apply Property_Max in H1; rewrite H1; auto.
Qed.

Theorem Theorem180_Change : forall x y,
  x ∈ C -> y ∈ C -> x ∉ W \/ y ∉ W -> x ≠ Φ -> y ≠ Φ ->
  P[x × y] = Max P[x] P[y].
Proof.
  intros; destruct H1.
  - apply Lemma180'; auto.
  - assert (x × y ≈ y × x); try apply Lemma180.
    assert (Ensemble (x × y) /\ Ensemble (y × x)).
    { split; apply set_cart; split; Ens. }
    apply card_eq in H5; apply H5 in H4; clear H5.
    rewrite H4, Equal_Max; apply Lemma180'; auto.
Qed.

Hint Resolve Theorem180_Not Theorem180_Change : set.


(* 181 Theorem  There is a unique ≺-≺ order-preserving function with domain R
   and range C ~ W.  *)

Theorem cont_hypo : exists f, Order_Pr f E E /\ dom(f) = R /\ ran(f) = C ~ W.
Proof.
  generalize ord_not_set_R; intros; destruct H; apply ord_well_order in H.
  assert ((C ~ W) ⊂ R).
  { unfold Subclass, Difference; intros; apply bel_inter in H1; destruct H1.
    unfold C in H1; apply Axiom_Scheme in H1; unfold Cardinal_Number in H1.
    destruct H1, H3; unfold Ordinal_Number in H3; auto. }
  apply lem_order_pre_sec_sub with (r:= E) in H1; auto; add (WellOrdered E (C ~ W)) H.
  clear H1; apply well_order_pre in H; destruct H as [f H], H, H1; exists f.
  destruct H1, H3, H4, H5; split; auto; destruct H2; split; auto.
  - rewrite <- H2 in H0; clear H2 H5.
    apply order_pre_fun1_inv in H4; destruct H4 as [H2 _], H2.
    generalize (classic (ran(f) = C ~ W)); intros; destruct H5; auto.
    assert (Ensemble ran(f)).
    { unfold Section in H6; destruct H6, H7 as [_ H7].
      assert (ran(f) ⊊ C ~ W); unfold ProperSubclass; auto.
      apply Property_ProperSubclass' in H8; destruct H8, H8.
      assert (ran(f) ⊂ x).
      { unfold Subclass; intros; double H10; apply H6 in H11.
        assert (x ∈ (C ~ W) /\ z ∈ (C ~ W)); auto.
        unfold WellOrdered in H3; destruct H3 as [H3 _].
        apply H3 in H12; destruct H12 as [H12 | [H12 | H12]].
        - destruct H9; apply H7 with (v:= z); auto.
        - unfold Rrelation, E in H12; apply Axiom_SchemeP in H12; apply H12.
        - rewrite H12 in H9; contradiction. }
      apply sub_set in H10; Ens. }
    rewrite dom_ran_inv in H0; rewrite dom_ran_inv' in H7.
    apply Axiom_Substitution in H7; auto; contradiction.
  - clear H3 H4 H0 H6.
    generalize (classic (dom(f) = R)); intros; destruct H0; auto.
    assert (~ Ensemble ran(f)).
    { rewrite H2; intro; generalize C_not_set, W_bel_C; intros.
      add (Ensemble W) H3; Ens; apply Axiom_Union in H3; clear H6.
      assert (C ~ W ∪ W = C).
      { apply Axiom_Extent; unfold Difference; split; intros.
        - apply bel_union in H6; destruct H6.
          + apply bel_inter in H6; apply H6.
          + generalize W_sub_C; intros; apply H7 in H6; auto.
        - generalize (classic (z ∈ W)); intros; apply bel_union.
          destruct H7; try tauto; left; apply bel_inter.
          split; auto; unfold Complement; apply Axiom_Scheme; Ens. }
      rewrite H6 in H3; contradiction. }
    assert (Ensemble dom(f)); clear H2.
    { intros; generalize ord_not_set_R; intros; destruct H2 as [H2 _]; double H5.
      apply sec_R_ord in H5; assert (Ordinal dom(f) /\ Ordinal R); auto.
      apply ord_bel_eq in H6; destruct H6 as [H6|[H6|H6]]; try tauto; Ens.
      apply H4 in H6; generalize (notin_fix R); intros; contradiction. }
    apply Axiom_Substitution in H4; auto; contradiction.
Qed.

Theorem cont_hypo' : forall f g,
  Order_Pr f E E -> Order_Pr g E E -> dom(f) = R -> dom(g) = R ->
  ran(f) = C ~ W -> ran(g) = C ~ W -> f = g.
Proof.
  intros.
  assert (Order_Pr f E E /\ Order_Pr g E E); auto.
  generalize ord_not_set_R; intros; destruct H6 as [H6 _]; apply ord_well_order in H6.
  assert ((C ~ W) ⊂ R).
  { unfold Subclass, Difference; intros; apply bel_inter in H7; destruct H7.
    unfold C in H7; apply Axiom_Scheme in H7; unfold Cardinal_Number in H7.
    destruct H7, H9; unfold Ordinal_Number in H9; auto. }
  apply lem_order_pre_sec_sub with (r:= E) in H7; auto.
  assert (Section dom(f) E R /\ Section dom(g) E R).
  { rewrite H1, H2; unfold Section, Subclass.
    split; try (repeat split; try apply H6; intros; auto; try apply H8). }
  assert (Section ran(f) E (C~W) /\ Section ran(g) E (C~W)).
  { rewrite H3, H4; unfold Section, Subclass.
    split; try (repeat split; try apply H7; intros; auto; try apply H9). }
  apply (order_pre_sec_sub f g E E R (C~W)) in H5; auto; clear H6 H7 H8 H9.
  unfold Order_Pr in H, H0; destruct H, H0, H5.
  - apply sub_eq; split; auto; unfold Subclass; intros.
    rewrite fun_set_eq; rewrite fun_set_eq in H8; auto; PP H8 a b.
    double H9; rewrite <- fun_set_eq in H9; auto; apply Axiom_SchemeP in H10.
    destruct H10; apply Axiom_SchemeP; split; auto; rewrite H11 in *.
    assert ([a,f[a]] ∈ f).
    { apply Property_Value; auto; apply Property_dom in H9.
      rewrite H2, <- H1 in H9; auto. }
    apply H5 in H12; eapply H0; eauto.
  - apply sub_eq; split; auto; unfold Subclass; intros.
    rewrite fun_set_eq; rewrite fun_set_eq in H8; auto; PP H8 a b.
    double H9; rewrite <- fun_set_eq in H9; auto; apply Axiom_SchemeP in H10.
    destruct H10; apply Axiom_SchemeP; split; auto; rewrite H11 in *.
    assert ([a,g[a]] ∈ g).
    { apply Property_Value; auto; apply Property_dom in H9.
      rewrite H1, <- H2 in H9; auto. }
    apply H5 in H12; eapply H; eauto.
Qed.

Hint Resolve cont_hypo cont_hypo' : set.

End Cardinal.

Export Cardinal.

