Require Export Functions.

(* WELL ORDERING *)

Module WellOrder.

(* 81 Definition  x r y if and only [x,y] ∈ r. *)

Definition Rrelation x r y : Prop := [x,y] ∈ r.

Hint Unfold Rrelation : set.


(* 82 Definition  r connects x if and only if when u and v belong to x either
   u r v or v r u or v = u. *)

Definition Connect r x : Prop := 
  forall u v, u∈x /\ v∈x -> (Rrelation u r v) \/ (Rrelation v r u) \/ (u=v).

Hint Unfold Connect : set.


(* 83 Definition  r is transitive in x if and only if, when u, v, and w
   are members of x and u r v and v r w, then u r w. *)

Definition Transitive r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x /\ Rrelation u r v /\  Rrelation v r w) ->
  Rrelation u r w.

Hint Unfold Transitive: set.


(* 84 Definition  r is asymmetric in x if and only if, when u and v are
   members of x and u r v, then it is not true that v r u. *)

Definition Asymmetric r x : Prop := 
  forall u v, (u ∈ x /\ v ∈ x /\ Rrelation u r v) -> ~ Rrelation v r u.

Corollary Property_Asy : forall r x u,
  Asymmetric r x -> u ∈ x -> ~ Rrelation u r u.
Proof.
  intros; intro. 
  unfold Asymmetric in H; eapply H; eauto.
Qed.

Hint Unfold Asymmetric: set.
Hint Resolve Property_Asy: set.


(* 85 Definition Inequality (x y:Class) := ~ (x = y) . *)

(* Notation "x ≠ y" := (Inequality x y) (at level 70). *)


(* 86 Definition  z is an r-first member of x if and only if z∈x and if y∈x,
   then it is false that y r z. *)

Definition FirstMember z r x : Prop :=
  z ∈ x /\ (forall y, y ∈ x -> ~ Rrelation y r z).

Hint Unfold FirstMember : set.


(* 87 Definition  r well-orders x if and only if r connects x and if y⊂x and
   y ≠ Φ, then there is an r-first member of y. *)

Definition WellOrdered r x : Prop :=
  Connect r x /\ (forall y, y ⊂ x /\ y ≠ Φ -> exists z, FirstMember z r y).

Hint Unfold WellOrdered : set.


(* 88 Theorem  If r well-orders x, then r is transitive in x and r is
   asymmetric in x. *)

Lemma Lemma88 : forall x u v w,
  Ensemble u -> Ensemble v -> Ensemble w -> 
  x ∈ ([u] ∪ [v] ∪ [w]) -> x = u \/ x= v \/ x = w.
Proof.
  intros.
  apply Theorem19 in H; apply Theorem19 in H0; apply Theorem19 in H1.
  apply Axiom_Scheme in H2; destruct H2, H3.
  - left; apply Axiom_Scheme in H3; destruct H3; auto.
  - apply Axiom_Scheme in H3; destruct H3, H4.
    + right; left; apply Axiom_Scheme in H4; destruct H4; auto.
    + right; right; apply Axiom_Scheme in H4; destruct H4; auto.
Qed.

Theorem Theorem88 : forall r x,
  WellOrdered r x -> Transitive r x /\ Asymmetric r x .
Proof.
  intros; generalize H; intro.
  unfold WellOrdered in H0; destruct H0.
  assert (Asymmetric r x).
  { unfold Asymmetric; intros.
    destruct H2, H3; AssE u; AssE v.
    assert (([u | v] ⊂ x) /\ ([u | v] ≠ Φ)).
    { split.
      - unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
        + apply Theorem19 in H5; apply Axiom_Scheme in H8.
          destruct H8; rewrite H9; auto.
        + apply Theorem19 in H6; apply Axiom_Scheme in H8.
          destruct H8; rewrite H9; auto.
      - apply Lemma35; exists u; apply Axiom_Scheme; split; auto;
        left; apply Axiom_Scheme; split; auto. }
  apply H1 in H7; destruct H7; unfold FirstMember in H7; destruct H7.
  apply Theorem46 in H7; auto; destruct H7; subst x0.
  - apply H8; apply Axiom_Scheme; split; auto; right; apply Axiom_Scheme; split; auto.
  - intro; apply H8 with u; auto.
    apply Axiom_Scheme; split; auto; left; apply Axiom_Scheme; split; auto. }
  split; auto; unfold Transitive; intros.
  - destruct H3, H4, H5, H6; unfold Connect in H0; specialize H0 with w u.
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    * assert (([u] ∪ [v] ∪ [w] ⊂ x) /\ ([u] ∪ [v] ∪ [w] ≠ Φ)).
      { split.
        - unfold Subclass; intros; apply Axiom_Scheme in H8.
          destruct H8 as [_ H8]; destruct H8.
          + AssE u; apply Theorem19 in H9; apply Axiom_Scheme in H8.
            destruct H8; rewrite H10; auto.
          + apply Axiom_Scheme in H8; destruct H8 as [_ H8]; destruct H8.
            * AssE v; apply Theorem19 in H9; apply Axiom_Scheme in H8.
              destruct H8; rewrite H10; auto.
            * AssE w; apply Theorem19 in H9; apply Axiom_Scheme in H8.
              destruct H8; rewrite H10; auto.
        - intro; generalize (Theorem16 u); intro.
          apply H9; rewrite <- H8; apply Axiom_Scheme; split; Ens.
          left; apply Axiom_Scheme; split; intros; auto; Ens. }
      apply H1 in H8; destruct H8.
      unfold FirstMember in H8; destruct H8.
      assert (u ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; left; apply Axiom_Scheme; split; Ens. }
      assert (v ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply Axiom_Scheme; split; Ens.
        left; apply Axiom_Scheme; split; Ens. }
      assert (w ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply Axiom_Scheme; split; Ens. 
        right; apply Axiom_Scheme; split; Ens. }
      apply Lemma88 in H8; Ens; destruct H8 as [H8|[H8|H8]]; subst x0.
      + apply H9 in H12; contradiction.
      + apply H9 in H10; contradiction.
      + apply H9 in H11; contradiction.
    * subst w; unfold Asymmetric in H2; absurd (Rrelation u r v); auto.
Qed.

Hint Resolve Theorem88: set.


(* 89 Definition  y is an r-section of x if and only if y⊂x, r well-orders x,
   and for each u and v such that u∈x, v∈y, and u r v it is true that u∈y. *)

Definition Section y r x : Prop :=
  y ⊂ x /\ WellOrdered r x /\
  (forall u v, (u ∈ x /\ v ∈ y /\ Rrelation u r v) -> u ∈ y).

Hint Unfold Section : set.


(* 90 Theorem  If n ≠ Φ and each member of n is an r-section of x, then ∪n and
   ∩n are r-sections of x. *)

Theorem Theorem90 : forall n x r,
  n ≠ Φ /\ (forall y, y ∈ n -> Section y r x) -> 
  Section (∩ n) r x /\ Section (∪ n) r x.
Proof.
  intros; destruct H; double H.
  apply Lemma35 in H; destruct H; double H; apply H0 in H.
  red in H; destruct H, H3; split; unfold Section; intros.
  - split; try split; auto; intros.
    + unfold Subclass; intros; apply Axiom_Scheme in H5.
      destruct H5; apply H6 in H2; auto.
    + destruct H5, H6; apply Axiom_Scheme; split; intros; Ens.
      apply Axiom_Scheme in H6; destruct H6; double H8; apply H0 in H8.
      unfold Section in H8; eapply H8; split; eauto.
  - split; try split; auto; intros.
    + unfold Subclass; intros; apply Axiom_Scheme in H5; destruct H5, H6, H6.
      apply H0 in H7; unfold Section in H7; destruct H7 as [H7 _]; auto.
    + destruct H5, H6; apply Axiom_Scheme; split; intros; Ens.
      apply Axiom_Scheme in H6; destruct H6, H8, H8.
      double H9; apply H0 in H9; unfold Section in H9; destruct H9, H11.
      exists x1; split; auto; eapply H12; split; eauto.
Qed.

Hint Resolve Theorem90 : set.


(* 91 Theorem  If y is an r-section of x an y≠x, then y = {u : u∈x and u r v}
   for some v in x. *)

Theorem Theorem91 : forall x y r,
  Section y r x /\ y≠x ->
  (exists v, v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \}).
Proof.
  intros; destruct H.
  assert (exists v0, FirstMember v0 r (x ~ y)).
  { unfold Section in H; destruct H, H1; unfold WellOrdered in H1; destruct H1.
    assert ((x ~ y) ⊂ x).
    { unfold Subclass; intros; apply Axiom_Scheme in H4; tauto. }
    generalize (classic (x ~ y = Φ)); intro; destruct H5.
    - apply Property_Φ in H; apply H in H5.
      apply Property_Ineq in H0; contradiction.
    - apply H3; split; auto. }
  destruct H1; unfold FirstMember in H1; destruct H1.
  exists x0; apply Axiom_Scheme in H1; destruct H1, H3.
  split; auto; apply Axiom_Extent; split; intros.
  unfold Section in H; destruct H, H6.
  - apply Axiom_Scheme; repeat split; Ens; assert (z ∈ x); auto.
    unfold WellOrdered in H6; destruct H6 as [H6 _]; unfold Connect in H6.
    specialize H6 with x0 z; destruct H6 as [H6 | [H6 | H6]]; auto.
    + assert (x0 ∈ y). { apply H7 with z; repeat split; auto. }
      apply Axiom_Scheme in H4; destruct H4; contradiction.
    + apply Axiom_Scheme in H4; destruct H4; subst x0; contradiction.
  - apply Axiom_Scheme in H5; destruct H5, H6.
    generalize (classic (z ∈ (x ~ y))); intro; destruct H8.
    + apply H2 in H8; contradiction.
    + generalize (classic (z ∈ y)); intro; destruct H9; auto.
      elim H8; apply Axiom_Scheme.
      repeat split; auto; apply Axiom_Scheme; tauto.
Qed.

Hint Resolve Theorem91 : set.


(* 92 Theorem  If x and y are r-sections of z, then x⊂y or y⊂x. *)

Theorem Theorem92 : forall x y z r,
  Section x r z /\ Section y r z -> x ⊂ y \/ y ⊂ x.
Proof.
  intros; destruct H.
  generalize (classic (x = z)); intro; destruct H1.
  - right; red in H0; subst z; tauto.
  - generalize (classic (y = z)); intro; destruct H2.
    + left; red in H; subst z; tauto.
    + apply Lemma_xy with (x:= (Section x r z)) in H1; auto.
      apply Lemma_xy with (x:= (Section y r z)) in H2; auto.
      apply Theorem91 in H1; destruct H1, H1.
      apply Theorem91 in H2; destruct H2, H2.
      unfold Section in H; destruct H as [_ [H _]].
      unfold WellOrdered in H; destruct H as [H _].
      unfold Section in H0; destruct H0, H5.
      apply Theorem88 in H5; destruct H5; unfold Transitive in H5.
      assert ((x0 ∈ z) /\ (x1 ∈ z)); try split; auto.
      unfold Connect in H; generalize (H _ _ H8); intros.
      destruct H9 as [H9 | [H9 | H9]].
      * left; unfold Subclass; intros; rewrite H3 in H10.
        apply Axiom_Scheme in H10; destruct H10, H11; rewrite H4.
        apply Axiom_Scheme.
        repeat split; auto; apply H5 with x0; auto.
      * right; unfold Subclass; intros; rewrite H4 in H10.
        apply Axiom_Scheme in H10; destruct H10, H11.
        rewrite H3; apply Axiom_Scheme.
        repeat split; auto; apply H5 with x1; auto.
      * right; subst x0; rewrite H3, H4; unfold Subclass; intros; auto.
Qed.

Hint Resolve Theorem92 : set.


(* 93 Definition  f is r-s order preserving if and only if f is a function,
   r well-orders domain f, s well-orders range f, and f[u] s f[v] whenever u
   and v are members of domain f such that u r v. *)

Definition Order_Pr f r s : Prop := 
  Function f /\ WellOrdered r dom(f) /\ WellOrdered s ran(f) /\
  (forall u v, u ∈ dom(f) /\ v ∈ dom(f) /\ Rrelation u r v ->
  Rrelation f[u] s f[v]).

Hint Unfold Order_Pr : set.


(* 94 Theorem  If x is an r-section of y and f is an r-r order-preserving
   function on x to y, then for each u in x it is false that f[u] r u. *)

Theorem Theorem94 : forall x r y f,
  Section x r y /\ Order_Pr f r r /\ On f x /\ To f y -> 
  (forall u, u ∈ x -> ~ Rrelation f[u] r u).
Proof.
  intros; destruct H, H1, H2.
  unfold Order_Pr in H1; destruct H1, H4, H5.
  unfold On in H2; destruct H2 as [H2 H7].
  unfold To in H3; destruct H3 as [_ H3].
  generalize (classic (\{ λ u, u ∈ x /\ Rrelation (Value f u) r u \} = Φ)).
  intros; destruct H8.
  - intro.
    assert (u ∈ Φ). { rewrite <- H8; apply Axiom_Scheme; repeat split; Ens. }
    generalize (Theorem16 u); intro; contradiction.
  - unfold Section in H; destruct H, H9.
    assert (\{ λ u, u ∈ x /\ Rrelation f [u] r u \} ⊂ y).
    { unfold Subclass; intros; apply Axiom_Scheme in H11; destruct H11, H12; auto. }
    unfold WellOrdered in H9; destruct H9.
    add (\{ λ u, u ∈ x /\ Rrelation f [u] r u \} ≠ Φ) H11.
    apply H12 in H11; destruct H11; unfold FirstMember in H11; destruct H11.
    apply Axiom_Scheme in H11; destruct H11, H14.
    assert (f[x0] ∈ ran( f)).
    { rewrite <- H7 in H14; apply Property_Value in H14; auto.
      apply Property_ran in H14; auto. }
    assert (f [x0] ∈ y); auto; subst x.
    assert (f [x0] ∈ \{ λ u, u ∈ dom( f) /\ Rrelation f [u] r u \}).
    { apply Axiom_Scheme; repeat split; try Ens.
      apply H6; repeat split; auto; apply H10 with x0; split; auto. }
    apply H13 in H7; contradiction.
Qed.

Hint Resolve Theorem94 : set.


(* 95 Definition  f is a 1_1 function iff both f and f⁻¹ are functions. *)

Definition Function1_1 f : Prop := Function f /\ Function (f⁻¹).

Hint Unfold Function1_1 : set.


(* 96 Theorem  If f is r-s order preserving, then f is a 1_1 function and
   f ⁻¹ is s-r order preserving. *)

Lemma Lemma96 : forall f, dom( f) = ran( f⁻¹ ).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
    exists x; apply Axiom_SchemeP; split; auto; apply Lemma61; Ens.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme.
    split; auto; exists x; apply Axiom_SchemeP in H0; tauto.
Qed.

Lemma Lemma96' : forall f, ran( f) = dom( f⁻¹ ).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
    exists x; apply Axiom_SchemeP; split; auto; apply Lemma61; Ens.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme.
    split; auto; exists x; apply Axiom_SchemeP in H0; tauto.
Qed.

Lemma Lemma96'' : forall f u,
  Function f -> Function f⁻¹ -> u ∈ ran(f) ->  (f⁻¹)[u] ∈ dom(f).
Proof.
  intros; rewrite Lemma96' in H1; apply Property_Value in H1; auto.
  apply Axiom_SchemeP in H1; destruct H1; apply Property_dom in H2; auto.
Qed.

Lemma Lemma96''' : forall f u,
  Function f -> Function f⁻¹ -> u ∈ ran(f) -> u = f[(f⁻¹)[u]].
Proof.
  intros; generalize (Lemma96'' _ _ H H0 H1); intro.
  apply Property_Value in H2; auto; rewrite Lemma96' in H1.
  apply Property_Value in H1; auto; apply Axiom_SchemeP in H1.
  destruct H1; red in H; destruct H; eapply H4; eauto.
Qed.

Theorem Theorem96 : forall f r s,
  Order_Pr f r s -> Function1_1 f /\ Order_Pr (f⁻¹) s r.
Proof.
  intros; unfold Order_Pr in H; destruct H, H0, H1.
  assert (Function1_1 f).
  { unfold Function1_1; split; auto; unfold Function; split; intros.
    - red; intros; PP H3 a b; Ens.
    - destruct H3; rename y into u; rename z into v.
      apply Axiom_SchemeP in H3; destruct H3; apply Axiom_SchemeP in H4.
      destruct H4; double H5; double H6.
      apply Property_dom in H5; apply Property_dom in H6.
      double H7; double H8; apply Property_dom in H7.
      apply Property_dom in H8; rewrite Theorem70 in H9; auto.
      apply Axiom_SchemeP in H9; destruct H9 as [_ H9].
      rewrite Theorem70 in H10; auto.
      apply Axiom_SchemeP in H10; destruct H10 as [_ H10].
      rewrite H10 in H9; symmetry in H9; clear H10.
      apply Property_Value in H7; apply Property_Value in H8; auto.
      apply Property_ran in H7; apply Property_ran in H8.
      double H0; double H1; apply Theorem88 in H11; destruct H11.
      unfold WellOrdered in H1; destruct H1 as [H1 _].
      unfold Connect in H1; specialize H1 with f [u] f [v].
      unfold WellOrdered in H0; destruct H0.
      unfold Connect in H0; specialize H0 with u v.
      destruct H0 as [H0 | [H0 | H0]]; try split; auto.
      + assert (Rrelation f [u] s f [v]); try apply H2; try tauto.
        rewrite H9 in H14; generalize (Property_Asy _ _ _ H12 H8).
        intro; contradiction.
      + assert (Rrelation f [v] s f [u]); try apply H2; try tauto.
        rewrite H9 in H14; generalize (Property_Asy _ _ _ H12 H8).
        intro; contradiction. }
  split; auto.
  - unfold Function1_1 in H3; destruct H3 as [_ H3]; unfold Order_Pr; intros.
    repeat rewrite <- Lemma96; repeat rewrite <- Lemma96'; split; auto.
    split; auto; split; intros; auto; destruct H4, H5.
    assert ((f⁻¹) [u] ∈ dom(f)); try apply Lemma96''; auto.
    assert ((f⁻¹) [v] ∈ dom(f)); try apply Lemma96''; auto.
    unfold WellOrdered in H0; destruct H0 as [H0 _]; unfold Connect in H0.
    specialize H0 with (f⁻¹) [u] (f⁻¹) [v].
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    + assert (Rrelation f  [(f⁻¹) [v]] s f [(f⁻¹) [u]] ); auto.
      rewrite <- Lemma96''' in H9; rewrite <- Lemma96''' in H9; auto.
      apply Theorem88 in H1; destruct H1; unfold Asymmetric in H10.
      generalize (Lemma_xy _ _ H5 (Lemma_xy _ _ H4 H9)); intro.
      generalize (H10 _ _ H11); intro; contradiction.
    + assert (f [(f⁻¹) [u]] = f [(f⁻¹) [v]]); rewrite H0; auto.
      rewrite <- Lemma96''' in H9; rewrite <- Lemma96''' in H9; auto.
      apply Theorem88 in H1; destruct H1.
      rewrite H9 in H6; apply Property_Asy with (r:=s) in H5; tauto.
Qed.

Hint Resolve Theorem96 : set.


(* 97 Theorem  If f and g are r-s order preserving, domain f and domain g are
   r-sections of x and range f and range g are s-sections of y, then f⊂g or
   g⊂f. *)

Lemma Lemma97 : forall y r x,
  WellOrdered r x -> y ⊂ x -> WellOrdered r y.
Proof.
  intros; unfold WellOrdered in H; destruct H.
  unfold WellOrdered; intros; split; intros.
  - red; intros.
    apply H; destruct H2; split; auto.
  - specialize H1 with y0.
    apply H1; destruct H2.
    split; auto; eapply Theorem28; eauto.
Qed.

Lemma Lemma97' :  forall f g u r s v x y,
  Order_Pr f r s /\ Order_Pr g r s -> 
  FirstMember u r (\{ λ a ,a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}) ->
  g[v] ∈ ran( g) -> Section ran( f) s y -> Section dom( f) r x -> 
  Section dom( g) r x -> Rrelation g [v] s g [u] -> 
  f[u] = g[v] -> f ⊂ g \/ g ⊂ f.
Proof.
  intros.
  unfold FirstMember in H0; destruct H0.
  apply Axiom_Scheme in H0; destruct H0, H8.
  apply Axiom_Scheme in H8; destruct H8 as [_ [H8 H10]].
  destruct H; unfold Order_Pr in H, H11.
  apply Property_Value in H8; apply Property_Value in H10; try tauto.
  apply Property_ran in H8; apply Property_ran in H10; auto.
  assert (Rrelation v r u).
  { elim H11; intros; clear H13.
    apply Theorem96 in H11; destruct H11 as [_ H11].
    red in H11; destruct H11 as [H11 [_ [_ H13]]].
    double H1; double H10; rewrite Lemma96' in H14, H15.
    apply Property_Value' in H10; auto; apply Property_dom in H10.
    rewrite Lemma96 in H10; apply Property_Value' in H1; auto.
    apply Property_dom in H1; rewrite Lemma96 in H1.
    rewrite Lemma96''' with (f:=g⁻¹); try (rewrite Theorem61; apply H12); auto.
    pattern v; rewrite Lemma96''' with (f:=(g⁻¹));
    try rewrite Theorem61; try apply H11; try apply H12; auto. }
  assert (v ∈ \{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a] \}).
  { apply Property_Value' in H1; try tauto; apply Property_dom in H1.
    apply Property_Value' in H8; try tauto; apply Property_dom in H8.
    apply Axiom_Scheme; repeat split; try Ens.
    - apply Axiom_Scheme; repeat split; try Ens.
      apply H3 with u; repeat split; auto.
      unfold Section in H4; apply H4; auto.
    - intro.
      assert (v ∈ dom(f)).
      { apply H3 with u; repeat split; auto; apply H4 in H1; auto. }
      assert (Rrelation f [v] s f [u]).
      { apply H; repeat split; auto. }
      rewrite H13 in H15; unfold Section in H2; destruct H2, H16.
      generalize (Lemma97 _ _ _ H16 H2); intro.
      apply Theorem88 in H18; destruct H18.
      rewrite <- H13 in H15; rewrite H6 in H15; rewrite <- H13 in H15.
      apply Property_Value in H14; try tauto; apply Property_ran in H14.
      generalize (Property_Asy _ _ _ H19 H14); intro; contradiction. }
  apply H7 in H13; contradiction.
Qed.

Lemma Lemma97'' : forall f g,
  \{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a] \} =
  \{ λ a, a ∈ (dom(g) ∩ dom(f)) /\ g[a] ≠ f[a] \}.
Proof.
  intros.
  apply Axiom_Extent; split; intros; rewrite Theorem6'; apply Axiom_Scheme in H;
  apply Axiom_Scheme; repeat split; try tauto; apply Property_Ineq; tauto.
Qed.

Lemma Lemma97''' : forall f g,
  f ⊂ g \/ g ⊂ f <-> g ⊂ f \/ f ⊂ g.
Proof.
  intros; split; intros; destruct H; tauto.
Qed.

Theorem Theorem97 : forall f g r s x y,
  Order_Pr f r s /\ Order_Pr g r s -> 
  Section dom(f) r x /\ Section dom(g) r x -> 
  Section ran(f) s y /\ Section ran(g) s y -> f ⊂ g \/ g ⊂ f.
Proof.
  intros; destruct H, H0, H1.
  assert (Order_Pr (g ⁻¹) s r).
  { apply Theorem96 in H2; tauto. }
  generalize (classic (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a] \} = Φ)).
  intro; destruct H6.
  - generalize (Lemma_xy _ _ H0 H3); intro.
    unfold Order_Pr in H; destruct H; unfold Order_Pr in H2; destruct H2.
    generalize (Theorem92 _ _ _ _ H7); intro; destruct H10.
    + left; unfold Subclass; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply Axiom_SchemeP in H13; destruct H13.
      rewrite Theorem70; auto; apply Axiom_SchemeP; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{ λ a, a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}).
      { apply Axiom_Scheme; split; Ens; split; auto.
        apply Theorem30 in H10; rewrite H10; auto. }
      eapply Axiom_Extent in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
    + right; unfold Subclass; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply Axiom_SchemeP in H13; destruct H13.
      rewrite Theorem70; auto; apply Axiom_SchemeP; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{ λ a, a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}).
      { apply Axiom_Scheme; split; Ens; split; auto. apply Theorem30 in H10.
        rewrite Theorem6' in H10; rewrite H10; auto. }
      eapply Axiom_Extent in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
  - assert (\{ λ a, a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \} ⊂ dom(f)).
    { unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
      apply Theorem4' in H8; tauto. }
    double H2; double H; unfold Order_Pr in H9; destruct H9, H10, H11.
    unfold WellOrdered in H10; destruct H10.
    generalize (Lemma_xy _ _ H7 H6); intro.
    apply H13 in H14; destruct H14 as [u H14].
    double H14; unfold FirstMember in H15; destruct H15.
    apply Axiom_Scheme in H15; destruct H15, H17.
    unfold Order_Pr in H2; destruct H2 as [H19 [_ [H2 _]]].
    apply Axiom_Scheme in H17; destruct H17 as [_ [H17 H20]].
    double H17; double H20.
    apply Property_Value in H17; apply Property_Value in H20; auto.
    apply Property_ran in H17; apply Property_ran in H20.
    generalize (Lemma_xy _ _ H1 H4); intro.
    apply Theorem92 in H23; auto; destruct H23.
    + apply H23 in H17; double H17.
      apply Axiom_Scheme in H17; destruct H17 as [_ [v H17]].
      rewrite Theorem70 in H17; auto; apply Axiom_SchemeP in H17.
      destruct H17; rewrite H25 in H24.
      generalize (Lemma_xy _ _ H24 H20); intro.
      unfold WellOrdered in H2; destruct H2 as [H2 _].
      unfold Connect in H2; apply H2 in H26.
      destruct H26 as [H26 | [H26 | H26]].
      * apply (Lemma97' f g u r s v x y); auto.
      * rewrite <- H25 in H26.
        assert (g [u] ∈ ran( f)).
        { unfold Section in H4; apply H4 in H20.
          unfold Section in H1; apply H1 with f[u]; repeat split; auto.
          apply Property_ran with u; apply Property_Value; auto. }
        double H27; apply Axiom_Scheme in H27; destruct H27 as [_ [v1 H27]].
        rewrite Theorem70 in H27; auto.
        apply Axiom_SchemeP in H27; destruct H27 as [_H27].
        rewrite H27 in H26, H28; rewrite Lemma97'' in H14; apply Lemma97'''.
        apply (Lemma97' g f u r s v1 x y); try tauto.
      * rewrite H26 in H25; contradiction.
    + apply H23 in H20; double H20.
      apply Axiom_Scheme in H20; destruct H20 as [_ [v H20]].
      rewrite Theorem70 in H20; auto.
      apply Axiom_SchemeP in H20; destruct H20; rewrite H25 in H24.
      generalize (Lemma_xy _ _ H17 H24); intro.
      unfold WellOrdered in H11; destruct H11 as [H11 _].
      unfold Connect in H11; apply H11 in H26.
      destruct H26 as [H26 | [H26 | H26]]; try contradiction.
      * rewrite <- H25 in H26.
        assert (f [u] ∈ ran( g)).
        { unfold Section in H1; apply H1 in H17.
          unfold Section in H4; eapply H4; repeat split; eauto.
          apply Property_ran with u; apply Property_Value; auto. }
        double H27; apply Axiom_Scheme in H27; destruct H27 as [_ [v1 H27]].
        rewrite Theorem70 in H27; auto; apply Axiom_SchemeP in H27.
        destruct H27 as [_H27]; rewrite H27 in H26, H28.
        apply (Lemma97' f g u r s v1 x y); try tauto.
      * rewrite Lemma97'' in H14; apply Lemma97'''.
        apply (Lemma97' g f u r s v x y); try tauto.
      * rewrite <- H25 in H26; contradiction.
Qed.

Hint Resolve Theorem97 : set.


(* 98 Definition  f is r-s order preserving in x and y if and only if r
   well-orders x, s well-orders y, f is r-s order preserving, domain f is an
   r-section of x, and range f is an s-section of y. *)

Definition Order_PXY f x y r s : Prop :=
  WellOrdered r x /\ WellOrdered s y /\ Order_Pr f r s /\
  Section dom(f) r x /\ Section ran(f) s y.

Hint Unfold Order_PXY : set.


(* 99 Theorem  If r well-orders x and s well-orders y, then there is a function
   f which is r-s order preserving in x and y such that either domain f = x or
   range f = y. *)

Definition En_f x y r s := 
  \{\ λ u v, u ∈ x /\ (exists g, Function g /\ Order_PXY g x y r s /\
  u ∈ dom(g) /\ [u,v] ∈ g ) \}\.

Lemma Lemma99 : forall y r x,
  WellOrdered r x -> Section y r x -> WellOrdered r y.
Proof.
  intros; red in H0; eapply Lemma97; eauto; tauto.
Qed.

Lemma Lemma99' : forall a b f z,
  ~ a ∈ dom(f) -> Ensemble a -> Ensemble b ->
  (z ∈ dom(f) -> (f ∪ [[a,b]]) [z] = f [z]).
Proof.
  intros; apply Axiom_Extent; split; intros; apply Axiom_Scheme in H3; destruct H3;
  apply Axiom_Scheme; split; intros; auto.
  - apply H4; apply Axiom_Scheme in H5; destruct H5; apply Axiom_Scheme; split; auto.
    apply Axiom_Scheme; split; Ens.
  - apply H4; apply Axiom_Scheme in H5; destruct H5.
    apply Axiom_Scheme in H6; destruct H6, H7; apply Axiom_Scheme; auto.
    assert ([a, b] ∈ μ). { apply Theorem19; apply Theorem49; tauto. }
    apply Axiom_Scheme in H7; destruct H7; apply H9 in H8.
    apply Theorem55 in H8; destruct H8; Ens.
    rewrite H8 in H2; contradiction.
Qed.

Lemma Lemma99'' : forall a b f z,
  ~ a ∈ dom(f) -> Ensemble a -> Ensemble b ->
  (z=a -> (f ∪ [[a,b]]) [z] = b).
Proof.
  intros; apply Axiom_Extent; split; intros; subst z.
  - apply Axiom_Scheme in H3; destruct H3; apply H3; apply Axiom_Scheme; split; auto.
    apply Axiom_Scheme; split; try apply Theorem49; try tauto.
    right; apply Axiom_Scheme; split; try apply Theorem49; try tauto.
  - apply Axiom_Scheme; split; intros; Ens.
    apply Axiom_Scheme in H2; destruct H2; apply Axiom_Scheme in H4; destruct H4, H5.
    + apply Property_dom in H5; contradiction.
    + apply Axiom_Scheme in H5; destruct H5.
      assert ([a, b] ∈ μ). { apply Theorem19; apply Theorem49; tauto. }
      generalize (H6 H7); intro; apply Theorem55 in H8;
      apply Theorem49 in H4; auto; destruct H8; rewrite H9; auto.
Qed.

Lemma Lemma99''' : forall y r x a b,  
  Section y r x -> a ∈ y -> ~ b ∈ y -> b ∈ x -> Rrelation a r b.
Proof.
  intros; unfold Section in H; destruct H, H3.
  unfold WellOrdered in H3; destruct H3; unfold Connect in H3.
  assert (a ∈ x); auto; generalize (Lemma_xy _ _ H2 H6); intro.
  apply H3 in H7; destruct H7 as [H7 | [H7 | H7]]; auto.
  - assert (b ∈ y). { eapply H4; eauto. } contradiction.
  - rewrite H7 in H1; contradiction.
Qed.

Theorem Theorem99 : forall r s x y,
  WellOrdered r x /\ WellOrdered s y ->
  exists f, Function f /\ Order_PXY f x y r s /\((dom(f) = x) \/ (ran(f) = y)).
Proof.
  intros.
  assert (Function (En_f x y r s)).
  { unfold Function; split; intros.
    - unfold Relation; intros; PP H0 a b; eauto.
    - destruct H0; apply Axiom_SchemeP in H0; destruct H0, H2, H3, H3, H4, H5.
      unfold Order_PXY in H4; destruct H4 as [_ [_ [H4 [H7 H8]]]].
      apply Axiom_SchemeP in H1; destruct H1, H9, H10, H10, H11, H12.
      unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H14 H15]]]].
      assert (x1 ⊂ x2 \/ x2 ⊂ x1). { apply (Theorem97 x1 x2 r s x y); tauto. }
      destruct H16.
      + apply H16 in H6; eapply H10; eauto.
      + apply H16 in H13; eapply H3; eauto. }
  exists (En_f x y r s); split; auto.
  assert (Section (dom(En_f x y r s)) r x).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; tauto.
    - split; try tauto; intros; destruct H1, H2.
      apply Axiom_Scheme in H2; destruct H2, H4.
      apply Axiom_SchemeP in H4; destruct H4, H5, H6; apply Axiom_Scheme; split; Ens.
      exists ((En_f x y r s)[u]); apply Property_Value; auto.
      apply Axiom_Scheme; split; Ens.
      assert (u ∈ dom( x1)).
      { destruct H6, H7; unfold Order_PXY in H7; destruct H7, H9, H10, H11.
        unfold Section in H11; destruct H11, H13; apply H14 with v.
        destruct H8; tauto. }
      exists (x1[u]); apply Axiom_SchemeP; repeat split; auto.
      + apply Theorem49; split; Ens.
        apply Theorem19; apply Theorem69; try tauto.
      + exists x1; split; try tauto; split; try tauto; split; auto.
        apply Property_Value; try tauto. }
  assert (Section (ran(En_f x y r s)) s y).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H2; destruct H2, H3.
      apply Axiom_SchemeP in H3; destruct H3, H4, H5, H5, H6, H7.
      unfold Order_PXY in H6; destruct H6 as [_ [_ [_ [_ H6]]]].
      unfold Section in H6; destruct H6 as [H6 _].
      apply Property_ran in H8; auto.
    - split; try tauto; intros; destruct H2, H3.
      apply Axiom_Scheme in H3; destruct H3, H5.
      apply Axiom_SchemeP in H5; destruct H5, H6, H7.
      apply Axiom_Scheme; split; Ens; exists (x1⁻¹[u]).
      apply Axiom_SchemeP; destruct H7 as [H7 [H8 [H9 H10]]]; double H8.
      unfold Order_PXY in H8; destruct H8 as [_ [_ [H12 [H13 H8]]]].
      generalize H11 as H20; intro.
      unfold Order_PXY in H11; destruct H11 as [H11 [_ H19]].
      unfold Section in H8; destruct H8 as [H8 [_ H15]].
      assert (u ∈ ran( x1)).
      { apply Property_ran in H10; apply H15 with v; tauto. }
      generalize H14 as H21; intro; apply Theorem96 in H12; destruct H12.
      unfold Function1_1 in H12; destruct H12; apply Lemma96'' in H14; auto.
      repeat split; auto.
      + apply Theorem49; split; Ens.
      + apply Property_Value in H14; auto. rewrite <- Lemma96''' in H14; auto.
        apply Property_dom in H14; destruct H19 as [_ [[H19 _] _]]; auto.
      + exists x1; split; try tauto; split; try tauto; split; auto.
        apply Property_Value in H14; auto; rewrite <- Lemma96''' in H14; auto. }
  assert (Order_PXY (En_f x y r s) x y r s).
  { unfold Order_PXY; split; try tauto; split; try tauto.
    split; [idtac | tauto]; unfold Order_Pr; split; auto.
    destruct H; split; try eapply Lemma99; eauto.
    split; intros; try eapply Lemma99; eauto.
    destruct H4, H5; double H4; double H5.
    apply Property_Value in H4; apply Property_Value in H5; auto.
    apply Axiom_SchemeP in H4; apply Axiom_SchemeP in H5.
    destruct H4 as [H4 [H9 [g1 [H10 [H11 [H12 H13]]]]]].
    destruct H5 as [H5 [H14 [g2 [H15 [H16 [H17 H18]]]]]].
    rewrite Theorem70 in H13; rewrite Theorem70 in H18; auto.
    apply Axiom_SchemeP in H13; destruct H13 as [_ H13].
    apply Axiom_SchemeP in H18; destruct H18 as [_ H18].
    rewrite H13, H18; clear H13 H18.
    unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H13 H18]]]].
    unfold Order_PXY in H16; destruct H16 as [_ [_ [H16 [H19 H20]]]].
    generalize (Lemma_xy _ _ H11 H16); intro.
    apply (Theorem97 g1 g2 r s x y) in H21; auto.
    apply Property_Value in H12; apply Property_Value in H17; auto.
    destruct H21.
    - apply H21 in H12; double H12; rewrite Theorem70 in H12; auto.
      apply Axiom_SchemeP in H12; destruct H12 as [_ H12]; rewrite H12.
      apply Property_dom in H22; apply Property_dom in H17; apply H16; tauto.
    - apply H21 in H17; double H17; rewrite Theorem70 in H17; auto.
      apply Axiom_SchemeP in H17; destruct H17 as [_ H17]; rewrite H17.
      apply Property_dom in H12; apply Property_dom in H22; apply H11; tauto. }
  split; auto; apply NNPP; intro; apply not_or_and in H4; destruct H4.
  assert (exists u, FirstMember u r (x ~ dom( En_f x y r s))).
  { unfold Section in H1; destruct H1, H6.
    assert ((x ~ dom( En_f x y r s)) ⊂ x).
    { red; intros; apply Axiom_Scheme in H8; tauto. }
    assert ((x ~ dom( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H1; apply H1 in H9; apply H4; auto. }
    generalize (Lemma97 _ _ _ H6 H8); intro.
    apply H10; repeat split; auto; red; auto. }
  assert (exists v, FirstMember v s (y ~ ran( En_f x y r s))).
  { unfold Section in H2; destruct H2, H7.
    assert ((y ~ ran( En_f x y r s)) ⊂ y).
    { red; intros; apply Axiom_Scheme in H9; tauto. }
    assert ((y ~ ran( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H2; apply H2 in H10; apply H5; auto. }
    generalize (Lemma97 _ _ _ H7 H9); intro.
    apply H11; repeat split; auto; red; auto. }
  destruct H6 as [u H6]; destruct H7 as [v H7].
  unfold FirstMember in H6; unfold FirstMember in H7; destruct H6, H7.
  apply Axiom_Scheme in H6; destruct H6 as [_ [H6 H10]].
  apply Axiom_Scheme in H10; destruct H10 as [_ H10].
  apply H10; apply Axiom_Scheme; split; Ens.
  exists v; apply Axiom_SchemeP.
  split; try apply Theorem49; split; try Ens.
  exists ((En_f x y r s) ∪ [[u,v]]).
  assert (Function (En_f x y r s ∪ [[u, v]])).
  { assert ([u, v] ∈ μ) as H18.
    { apply Theorem19; apply Theorem49; split; try Ens. }
    unfold Function; split; intros.
    - unfold Relation; intros.
      apply Axiom_Scheme in H11; destruct H11 as [H11 [H12 | H12]].
      + PP H12 a b; eauto.
      + apply Axiom_Scheme in H12; exists u,v; apply H12; auto.
    - destruct H11; apply Axiom_Scheme in H11; apply Axiom_Scheme in H12.
      destruct H11 as [H11 [H13 | H13]], H12 as [H12 [H14 | H14]].
      + unfold Function in H0; eapply H0; eauto.
      + apply Property_dom in H13; apply Axiom_Scheme in H14; destruct H14.
        apply Theorem55 in H15; apply Theorem49 in H12; auto.
        destruct H15; rewrite H15 in H13; contradiction.
      + apply Property_dom in H14; apply Axiom_Scheme in H13; destruct H13.
        apply Theorem55 in H15; apply Theorem49 in H11; auto.
        destruct H15; rewrite H15 in H14; contradiction.
      + apply Axiom_Scheme in H13; destruct H13; apply Theorem55 in H15;
        apply Theorem49 in H13; auto.
        apply Axiom_Scheme in H14; destruct H14; apply Theorem55 in H16; 
        apply Theorem49 in H12; auto.
        destruct H15, H16; rewrite H17; auto. }
  split; auto.
  assert (Section (dom(En_f x y r s ∪ [[u, v]])) r x).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H12; destruct H12, H13.
      apply Axiom_Scheme in H13; destruct H13, H14.
      + apply Property_dom in H14; unfold Section in H1; apply H1; auto.
      + apply Axiom_Scheme in H14; destruct H14.
        assert ([u, v] ∈ μ).
        { apply Theorem19; apply Theorem49; split; try Ens. }
        apply H15 in H16; apply Theorem55 in H16; apply Theorem49 in H13; auto.
        destruct H16; rewrite H16; auto.
    - split; try tauto; intros; destruct H12, H13.
      apply Axiom_Scheme in H13; destruct H13, H15.
      apply Axiom_Scheme in H15; destruct H15, H16.
      + apply Axiom_Scheme; split; Ens.
        assert ([u0, (En_f x y r s) [u0]] ∈ (En_f x y r s)).
        { apply Property_dom in H16; apply Property_Value; auto.
          apply H1 with v0; repeat split; auto. }
        exists (En_f x y r s) [u0]; apply Axiom_Scheme; split; Ens.
      + apply Axiom_Scheme in H16; destruct H16.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H17 in H18; apply Theorem55 in H18;
        apply Theorem49 in H16; auto; destruct H18; subst v0.
        assert ([u0, (En_f x y r s) [u0]] ∈ (En_f x y r s)).
        { apply Property_Value; auto.
          generalize (classic (u0 ∈ dom( En_f x y r s))); intro.
          destruct H18; auto; absurd (Rrelation u0 r u); auto.
          apply H8; apply Axiom_Scheme; repeat split; Ens.
          apply Axiom_Scheme; split; Ens. }
        apply Axiom_Scheme; split; Ens.
        exists ((En_f x y r s)[u0]); apply Axiom_Scheme; split; Ens. }
  assert (Section (ran(En_f x y r s ∪ [[u, v]])) s y).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H13; destruct H13, H14.
      apply Axiom_Scheme in H7; destruct H7 as [_ [H7 _]] .
      apply Axiom_Scheme in H14; destruct H14, H15.
      + apply Property_ran in H15; unfold Section in H2; apply H2; auto.
      + apply Axiom_Scheme in H15; destruct H15.
        assert ([u, v] ∈ μ).
        { apply Theorem19; apply Theorem49; split; try Ens. }
        apply H16 in H17; apply Theorem55 in H17;
        apply Theorem49 in H14; auto; destruct H17; rewrite H18; auto.
    - split; try tauto; intros; destruct H13, H14.
      apply Axiom_Scheme in H14; destruct H14, H16.
      unfold Order_PXY in H3; destruct H3 as [_ [_ [H3 _]]].
      apply Theorem96 in H3; destruct H3 as [[_ H3] _].
      apply Axiom_Scheme in H16; destruct H16, H17.
      + apply Axiom_Scheme; split; Ens.
        assert ([((En_f x y r s) ⁻¹) [u0], u0] ∈ (En_f x y r s)).
        { assert (u0 ∈ ran( En_f x y r s)).
          { apply Property_ran in H17; apply H2 with v0; repeat split; auto. }
          pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
          apply Property_Value'; auto; rewrite <- Lemma96'''; auto. }
        exists ((En_f x y r s) ⁻¹) [u0]; apply Axiom_Scheme; split; Ens.
      + apply Axiom_Scheme in H17; destruct H17.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H18 in H19; apply Theorem55 in H19;
        apply Theorem49 in H16; auto; destruct H19; subst v0.
        assert ([((En_f x y r s) ⁻¹) [u0], u0] ∈ (En_f x y r s)).
        { generalize (classic (u0 ∈ ran( En_f x y r s))); intro; destruct H20.
          - pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
            apply Property_Value'; auto; rewrite <- Lemma96'''; auto.
          - absurd (Rrelation u0 s v); auto.
            apply H9; apply Axiom_Scheme; repeat split; Ens.
            apply Axiom_Scheme; split; Ens. }
        apply Axiom_Scheme; split; Ens.
        exists ((En_f x y r s) ⁻¹) [u0]; apply Axiom_Scheme; split; Ens. }
  split.
  - unfold Order_PXY; split; try tauto.
    split; try tauto; split; [idtac | tauto].
    unfold Order_Pr; intros; split; auto.
    split; try eapply Lemma99; eauto; try apply H.
    split; try eapply Lemma99; eauto; try apply H; intros.
    destruct H14, H15; apply Axiom_Scheme in H14; destruct H14, H17.
    apply Axiom_Scheme in H17; destruct H17 as [_ H17].
    apply Axiom_Scheme in H15; destruct H15, H18.
    apply Axiom_Scheme in H18; destruct H18 as [_ H18].
    assert ([u,v] ∈ μ) as H20.
    { apply Theorem19; apply Theorem49; split; Ens. }
    destruct H17, H18.
    + apply Property_dom in H17; apply Property_dom in H18;
      repeat rewrite Lemma99'; auto; Ens.
      unfold Order_PXY in H3; destruct H3 as [_ [_ [H3 _]]].
      unfold Order_Pr in H3; eapply H3; eauto.
    + apply Property_dom in H17; rewrite Lemma99'; auto; Ens.
      apply Axiom_Scheme in H18; destruct H18.
      apply H19 in H20;  apply Theorem55 in H20; destruct H20;
      apply Theorem49 in H18; auto; rewrite Lemma99''; auto; Ens.
      apply Lemma99''' with (y:=(ran( En_f x y r s))) (x:=y); auto.
      * apply Property_Value in H17; auto.
        double H17; apply Property_ran in H17.
        apply Axiom_Scheme; split; Ens; exists u0; apply Axiom_Scheme; split; Ens.
      * apply Axiom_Scheme in H7; destruct H7, H22; apply Axiom_Scheme in H23; tauto.
      * apply Axiom_Scheme in H7; tauto.
    + apply Property_dom in H18.
      pattern ((En_f x y r s ∪ [[u, v]]) [v0]); rewrite Lemma99'; Ens.
      assert (u0 ∈ dom( En_f x y r s)).
      { unfold Section in H1; apply H1 with v0; split; auto.
        apply Axiom_Scheme in H17; destruct H17; apply H19 in H20.
        apply Theorem55 in H20; apply Theorem49 in H17; auto.
        destruct H20; rewrite H20; auto. }
      rewrite Lemma99'; Ens; unfold Order_PXY in H3.
      destruct H3 as [_ [_ [H3 _]]]; unfold Order_Pr in H3; eapply H3; eauto.
    + double H20; apply Axiom_Scheme in H17; destruct H17; apply H21 in H19.
      apply Axiom_Scheme in H18; destruct H18; apply H22 in H20.
      apply Theorem55 in H20; destruct H20; apply Theorem49 in H18; auto.
      apply Theorem55 in H19; destruct H19; apply Theorem49 in H17; auto.
      subst u0 v0; destruct H as [H _]; apply Theorem88 in H.
      destruct H as [_ H]; apply Property_Asy with (u:=u) in H; auto.
      contradiction.
  - assert (Ensemble ([u,v])). { apply Theorem49; split; Ens. } split.
    + apply Axiom_Scheme; split; Ens; exists v; apply Axiom_Scheme; split; Ens.
      right; apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem99 : set.


(* 100 Theorem  If r well-orders x, s well-orders y, x is a set, and y is not
   a set, then there is a unique r-s order-preserving function in x and y whose
   domain is x. *)

Theorem Theorem100 : forall r s x y,
  WellOrdered r x /\ WellOrdered s y -> Ensemble x -> ~ Ensemble y ->
  exists f, Function f /\ Order_PXY f x y r s /\ dom( f) = x.
Proof.
  intros; destruct H.
  generalize (Lemma_xy _ _ H H2); intro.
  apply Theorem99 in H3; destruct H3, H3, H4.
  exists x0; split; auto; split; auto; destruct H5; auto.
  unfold Order_PXY in H4; destruct H4 as [_ [_ [_ [H4 _]]]].
  unfold Section in H4; destruct H4; apply Theorem33 in H4; auto.
  apply Axiom_Substitution in H4; auto; rewrite H5 in H4; contradiction.
Qed.

Theorem Theorem100' : forall r s x y,
  WellOrdered r x /\ WellOrdered s y -> Ensemble x -> ~ Ensemble y ->
  forall f, Function f /\ Order_PXY f x y r s /\ dom(f) = x ->
  forall g, Function g /\ Order_PXY g x y r s /\ dom(g) = x -> f = g.
Proof.
  intros; destruct H, H2, H5, H3, H7; unfold Order_PXY in H5, H7.
  destruct H5 as [_ [_ H5]], H5, H9, H7 as [_ [_ H7]], H7, H11.
  generalize (Lemma_xy _ _ H5 H7); intro.
  apply (Theorem97 f g r s x y) in H13; auto; destruct H13.
  - apply Theorem27; split; auto; unfold Subclass; intros.
    rewrite Theorem70; rewrite Theorem70 in H14; auto.
    PP H14 a b; double H15; rewrite <- Theorem70 in H15; auto.
    apply Axiom_SchemeP in H16; destruct H16.
    apply Axiom_SchemeP; split; auto; rewrite H17 in *.
    assert ([a,f[a]] ∈ f).
    { apply Property_Value; auto; subst x.
      apply Property_dom in H15; rewrite <- H8; auto. }
    apply H13 in H18; eapply H3; eauto.
  - apply Theorem27; split; auto; unfold Subclass; intros.
    rewrite Theorem70; rewrite Theorem70 in H14; auto.
    PP H14 a b; double H15; rewrite <- Theorem70 in H15; auto.
    apply Axiom_SchemeP in H16; destruct H16.
    apply Axiom_SchemeP; split; auto; rewrite H17 in *.
    assert ([a,g[a]] ∈ g).
    { apply Property_Value; auto; subst x.
      apply Property_dom in H15; rewrite H8; auto. }
    apply H13 in H18; eapply H2; eauto.
Qed.

Hint Resolve Theorem100 Theorem100' : set.


End WellOrder.

Export WellOrder.

