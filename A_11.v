Require Export A_10.

(* "x ∈ y", "x ∪ y", "x ∩ y", "x ∉ y", "¬ x", "x ~ y", "x ≠ y", "Φ", "μ" *)
(* "∩ x", "∪ x", "x ⊂ y", "pow( x )", "[ x ]", "[ x | y ]", "[ x , y ]" *)
(* "r ⁻¹", "dom( f )", "ran( f )", "f [ x ]", "x × y" *)

(* A.11 基数 *)

Module A11.

(* 定义144 x≈y当且仅当存在一个1-1函数f，f的定义域=x而f的值域=y *)

Definition Equivalent x y : Prop :=
  exists f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.

Notation "x ≈ y" := (Equivalent x y) (at level 70).

Hint Unfold Equivalent : set.


(* 定理145 x≈x *)

Theorem Theorem145 : forall x, x ≈ x.
Proof.
  intros.
  unfold Equivalent.
  exists (\{\ λ u v, u ∈ x /\ u = v \}\); split.
  - unfold Function1_1; split.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H a b; Ens.
      * destruct H; apply AxiomII_P in H.
        apply AxiomII_P in H0; destruct H, H0, H1, H2.
        rewrite <- H3, <- H4; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H a b; Ens.
      * unfold Inverse in H; destruct H; apply AxiomII_P in H.
        apply AxiomII_P in H0; destruct H, H0.
        apply AxiomII_P in H1; apply AxiomII_P in H2.
        destruct H1, H2, H3, H4; rewrite H5, H6; auto.
   - split.
     + apply AxiomI; split; intros.
       * unfold Domain in H; apply AxiomII in H; destruct H, H0.
         apply AxiomII_P in H0; apply H0.
       * unfold Domain; apply AxiomII; split; Ens.
         exists z; apply AxiomII_P; repeat split; auto.
         apply Theorem49; split; Ens.
     + apply AxiomI; split; intros.
       * unfold Range in H; apply AxiomII in H; destruct H, H0.
         apply AxiomII_P in H0; destruct H0, H1.
         rewrite H2 in H1; auto.
       * unfold Range; apply AxiomII; split; Ens.
         exists z; apply AxiomII_P; repeat split; auto.
         apply Theorem49; split; Ens.
Qed.

Hint Resolve Theorem145 : set.


(* 定理146 如果x≈y，则y≈x *)

Theorem Theorem146 : forall x y, x ≈ y -> y ≈ x.
Proof.
  intros.
  unfold Equivalent in H; destruct H as [f H], H, H0.
  unfold Equivalent; exists f⁻¹; split.
  - unfold Function1_1 in H; destruct H.
    unfold Function1_1; split; try rewrite Theorem61; auto.
  - unfold Inverse; split.
    + unfold Domain; apply AxiomI; split; intros.
      * apply AxiomII in H2; destruct H2, H3.
        apply AxiomII_P in H3; destruct H3.
        apply Property_ran in H4; rewrite H1 in H4; auto.
      * apply AxiomII; split; Ens.
        rewrite <- H1 in H2; unfold Range in H2.
        apply AxiomII in H2; destruct H2, H3.
        exists (x0); apply AxiomII_P; split; auto.
        apply Theorem49; AssE ([x0,z]).
        apply Theorem49 in H4; destruct H4; Ens.
    + unfold Range; apply AxiomI; split; intros.
      * apply AxiomII in H2; destruct H2, H3.
        apply AxiomII_P in H3; destruct H3.
        apply Property_dom in H4; rewrite H0 in H4; auto.
      * apply AxiomII; split; Ens.
        rewrite <- H0 in H2; unfold Domain in H2.
        apply AxiomII in H2; destruct H2, H3.
        exists (x0); apply AxiomII_P; split; auto.
        apply Theorem49; AssE ([z,x0]).
        apply Theorem49 in H4; destruct H4; Ens.
Qed.

Hint Resolve Theorem146 : set.


(* 定理147 如果x≈y同时y≈z，则x≈z *)

Theorem Theorem147 : forall x y z,
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
      * destruct H7; apply AxiomII_P in H7; destruct H7, H9.
        apply AxiomII_P in H8; destruct H8, H10; clear H7 H8.
        unfold Function in H, H0; destruct H9, H10, H, H0.
        add ([x0,x2] ∈ f1) H7; apply H11 in H7; rewrite H7 in H8.
        add ([x2,z0] ∈ f2) H8; apply H12 in H8; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H7 a b; Ens.
      * unfold Inverse in H7; destruct H7; apply AxiomII_P in H7.
        apply AxiomII_P in H8; destruct H7, H8; clear H7 H8.
        apply AxiomII_P in H9; destruct H9, H8.
        apply AxiomII_P in H10; destruct H10, H10; clear H7 H9.
        unfold Function in H5, H6; destruct H8, H10, H5, H6.
        assert ([x0,x1] ∈ f2⁻¹ /\ [x0,x2] ∈ f2⁻¹).
        { unfold Inverse; split.
          - apply AxiomII_P; split; auto; AssE [x1,x0].
            apply Theorem49 in H13; destruct H13.
            apply Theorem49; split; auto.
          - apply AxiomII_P; split; auto; AssE [x2,x0].
            apply Theorem49 in H13; destruct H13.
            apply Theorem49; split; auto. }
        apply H12 in H13; rewrite H13 in H7; clear H8 H10 H12 H13.
        assert ([x2,y0] ∈ f1⁻¹ /\ [x2,z0] ∈ f1⁻¹).
        { unfold Inverse; split.
          - apply AxiomII_P; split; auto; AssE [y0,x2].
            apply Theorem49 in H8; destruct H8.
            apply Theorem49; split; auto.
          - apply AxiomII_P; split; auto; AssE [z0,x2].
            apply Theorem49 in H8; destruct H8.
            apply Theorem49; split; auto. }
        apply H11 in H8; auto.
  - rewrite <- H1, <- H4; split.
    + apply AxiomI; split; intros.
      * apply AxiomII in H5; destruct H5, H6.
        apply AxiomII_P in H6; destruct H6, H7, H7.
        apply Property_dom in H7; auto.
      * apply AxiomII; split; Ens; apply AxiomII in H5.
        destruct H5, H6; double H6; apply Property_ran in H7.
        rewrite H3 in H7; rewrite <- H2 in H7; apply AxiomII in H7.
        destruct H7, H8; exists x1; apply AxiomII_P; split; Ens.
        AssE [z0,x0]; AssE [x0,x1]; apply Theorem49 in H9.
        apply Theorem49 in H10; destruct H9, H10.
        apply Theorem49; split; auto.
    + apply AxiomI; split; intros.
      * apply AxiomII in H5; destruct H5, H6.
        apply AxiomII_P in H6; destruct H6, H7, H7.
        apply Property_ran in H8; auto.
      * apply AxiomII; split; Ens; apply AxiomII in H5.
        destruct H5, H6; double H6; apply Property_dom in H7.
        rewrite H2 in H7; rewrite <- H3 in H7; apply AxiomII in H7.
        destruct H7, H8; exists x1; apply AxiomII_P; split; Ens.
        AssE [x0,z0]; AssE [x1,x0]; apply Theorem49 in H9.
        apply Theorem49 in H10; destruct H9, H10.
        apply Theorem49; split; auto.
Qed.

Hint Resolve Theorem147 : set.


(* 定义148 x是一个基数就是说x是一个序数，并且如果y∈R和y≺x，则x≈y不真 *)

Definition Cardinal_Number x : Prop :=
  Ordinal_Number x /\ (forall y, y∈R -> y ≺ x -> ~ (x ≈ y)).

Hint Unfold Cardinal_Number : set.


(* 定义149 C = { x : x 是基数 } *)

Definition C : Class := \{ λ x, Cardinal_Number x \}.

Hint Unfold C : set.


(* 定理150 E良序C *)

Theorem Theorem150 : WellOrdered E C.
Proof.
  intros.
  unfold WellOrdered; split; intros.
  - unfold Connect; intros; destruct H; unfold C in H, H0.
    apply AxiomII in H; apply AxiomII in H0; destruct H, H0.
    unfold Cardinal_Number in H1, H2; destruct H1, H2; clear H3 H4.
    unfold Ordinal_Number, R in H1, H2; apply AxiomII in H1.
    apply AxiomII in H2; destruct H1, H2; add (Ordinal v) H3.
    clear H1 H2 H4; apply Theorem110 in H3; destruct H3.
    + left; unfold Rrelation, E; apply AxiomII_P.
      split; try apply Theorem49; auto.
    + destruct H1; auto; right; left; unfold Rrelation, E.
      apply AxiomII_P; split; try apply Theorem49; auto.
  - destruct H; assert (y ⊂ R).
    { unfold Included; intros; unfold Included in H.
      apply H in H1; unfold C in H1; apply AxiomII in H1.
      destruct H1; unfold Cardinal_Number in H2; destruct H2.
      unfold Ordinal_Number in H2; auto. }
    add (y ≠ Φ) H1; apply Lemma121 in H1; Ens.
Qed.

Hint Resolve Theorem150 : set.


(* 定义151 P = { (x,y) : x ≈ y 且 y ∈ C } *)

Definition P : Class := \{\ λ x y, x ≈ y /\ y ∈ C \}\.

Hint Unfold P : set.


(* 定理152 P是一个函数，P的定义域的=μ且P的值域=C *)

Theorem Theorem152 : Function P /\ dom(P) = μ /\ ran(P) = C.
Proof.
  unfold P; repeat split; intros.
  - unfold Relation; intros; PP H a b; Ens.
  - destruct H; apply AxiomII_P in H; apply AxiomII_P in H0.
    destruct H, H0, H1, H2; apply Theorem146 in H1.
    apply (Theorem147 _ _ z) in H1; auto; clear H H0 H2.
    unfold C in H3, H4; apply AxiomII in H3; destruct H3.
    apply AxiomII in H4; destruct H4.
    unfold Cardinal_Number in H0, H3; destruct H0, H3.
    unfold Ordinal_Number in H0, H3.
    assert (Ordinal y /\ Ordinal z).
    { unfold R in H0, H3; apply AxiomII in H0.
      apply AxiomII in H3; destruct H0, H3; split; auto. }
    apply Theorem110 in H6; destruct H6.
    + apply Theorem146 in H1; apply H5 in H0; auto; try contradiction.
    + destruct H6; auto; apply H4 in H3; auto; try contradiction.
  - apply AxiomI; split; intros; try apply Theorem19; Ens.
    apply Theorem19 in H; double H; apply Theorem140 in H0.
    destruct H0 as [f H0], H0, H1; apply AxiomII; split; auto.
    assert (WellOrdered E \{ λ x, x ≈ z /\ Ordinal x \}).
    { assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ R).
      { unfold Included; intros; apply AxiomII in H3.
        destruct H3, H4; apply AxiomII; split; auto. }
      apply (Lemma97 _ E _) in H3; auto.
      apply Theorem107; apply Theorem113. }
    unfold WellOrdered in H3; destruct H3 as [H4 H3]; clear H4.
    assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ \{ λ x, x ≈ z /\ Ordinal x \}
            /\ \{ λ x, x ≈ z /\ Ordinal x \} ≠ Φ).
    { split; try unfold Included; auto.
      apply Lemma35; exists dom(f); apply AxiomII.
      unfold Ordinal_Number, R in H2; apply AxiomII in H2; destruct H2.
      split; auto; split; auto; unfold Equivalent; exists f; auto. }
    apply H3 in H4; destruct H4; unfold FirstMember in H4; destruct H4.
    apply AxiomII in H4; destruct H4, H6.
    exists x; apply AxiomII_P.
    repeat split; try apply Theorem49; auto.
    + apply Theorem146; unfold Equivalent; Ens.
    + unfold C; apply AxiomII; split; auto.
      unfold Cardinal_Number; split; intros.
      { unfold Ordinal_Number, R; apply AxiomII; auto. }
      { unfold Less in H9; unfold R in H8.
        apply AxiomII in H8; destruct H8; intro.
        assert (y ∈ \{ λ x,x ≈ z /\ Ordinal x \}).
        { apply AxiomII; split; auto; split; auto.
          apply Theorem146 in H11; apply (Theorem147 _ x _); auto. }
        apply H5 in H12; apply H12; unfold Rrelation, E.
        apply AxiomII_P; split; try apply Theorem49; auto. }
  - unfold Range; apply AxiomI; split; intros.
    + apply AxiomII in H; destruct H, H0.
      apply AxiomII_P in H0; apply H0.
    + apply AxiomII; split; Ens; exists z; apply AxiomII_P.
      repeat split; try apply Theorem49; Ens.
      apply Theorem145.
Qed.

Hint Resolve Theorem152 : set.


(* 定义151的推论 *)

Corollary Property_PClass : forall x, Ensemble x -> P [x] ∈ C.
Proof.
  intros.
  generalize Theorem152; intros; destruct H0, H1.
  apply Theorem19 in H; rewrite <- H1 in H.
  apply Property_Value in H; auto.
  apply Property_ran in H; rewrite H2 in H; auto.
Qed.

Hint Resolve Property_PClass : set.


(* 定理153 如果x是一个集，则P[x]≈x *)

Theorem Theorem153 : forall x, Ensemble x -> P[x] ≈ x.
Proof.
  intros.
  generalize Theorem152; intros; destruct H0, H1.
  apply Theorem19 in H; rewrite <- H1 in H.
  apply Property_Value in H; auto.
  unfold P at 2 in H; apply AxiomII_P in H.
  apply Theorem146; apply H.
Qed.

Hint Resolve Theorem153 : set.


(* 定理154 如果x与y均为集，则当且仅当P(x)=P(y)时，x≈y *)

Theorem Theorem154 : forall x y,
  Ensemble x /\ Ensemble y -> (P[x] = P[y] <-> x ≈ y).
Proof.
  intros; double H; destruct H, H0.
  apply Theorem153 in H0; apply Theorem153 in H2; split; intros.
  - rewrite H3 in H0; apply Theorem146 in H0.
    apply (Theorem147 _ P[y] _); auto.
  - generalize Theorem152; intros; destruct H4, H5.
    double H; apply Theorem19 in H; apply Theorem19 in H1.
    rewrite <- H5 in H, H1; apply Property_Value in H; auto.
    apply Property_Value in H1; auto; apply Property_ran in H1.
    rewrite H6 in H1; apply Theorem146 in H2.
    assert ([x, P [y]] ∈ P).
    { unfold P at 2; apply AxiomII_P; split.
      - apply Theorem49; split; Ens.
      - split; try apply (Theorem147 _ y _); auto. }
    unfold Function in H4; apply H4 with (x:=x); auto.
Qed.

Hint Resolve Theorem154 : set.


(* 定理155 P[P[x]] = P[x] *)

Lemma Lemma155 : forall x, x ∈ C -> Ensemble x -> P[x] = x.
Proof.
  intros.
  double H0; apply Property_PClass in H1; AssE P[x].
  unfold C in H, H1; apply AxiomII in H; apply AxiomII in H1.
  clear H0 H2; destruct H, H1, H0, H2.
  apply Theorem153 in H; unfold Ordinal_Number in H0, H2.
  double H0; double H2; unfold R in H5, H6; apply AxiomII in H5.
  apply AxiomII in H6; destruct H5, H6; add (Ordinal P[x]) H7.
  clear H1 H5 H6 H8; apply Theorem110 in H7; destruct H7.
  + apply H4 in H1; auto; contradiction.
  + symmetry; destruct H1; auto; apply H3 in H1; auto.
    apply Theorem146 in H; contradiction.
Qed.

Theorem Theorem155 : forall x, P[P[x]] = P[x].
Proof.
  intros.
  generalize Theorem152; intros; destruct H, H0.
  generalize (classic (Ensemble x)); intros; destruct H2.
  - apply Property_PClass in H2; AssE P[x].
    apply Lemma155 in H2; auto.
  - generalize (classic (x ∈ dom(P))); intros; destruct H3.
    + rewrite H0 in H3; apply Theorem19 in H3; contradiction.
    + apply Theorem69 in H3; rewrite H3.
      generalize (classic (μ ∈ dom(P))); intros; destruct H4.
      * generalize Theorem39; intros; elim H5; Ens.
      * apply Theorem69 in H4; rewrite H4; auto.
Qed.

Hint Resolve Lemma155 Theorem155 : set.


(* 定理156 当且仅当x是一个集并且P[x]=x时，x∈C成立 *)

Theorem Theorem156 : forall x,
  (Ensemble x /\ P[x] = x) <-> x∈C.
Proof.
  intros; split; intros.
  - destruct H; apply Property_PClass in H.
    rewrite H0 in H; auto.
  - AssE x; apply Lemma155 in H; auto.
Qed.

Hint Resolve Theorem156 : set.


(* 定理157 如果y∈R且x⊂y，则P(x)≼y *)

Theorem Theorem157 : forall x y,
  y ∈ R /\ x ⊂ y -> P[x] ≼ y.
Proof.
  intros; destruct H.
  unfold R in H; apply AxiomII in H; destruct H.
  assert (WellOrdered E x /\ WellOrdered E R).
  { split; try (apply Theorem107; apply Theorem113).
    apply Theorem107 in H1; apply (Lemma97 _ _ y); auto. }
  assert (Ensemble x /\ ~ Ensemble R).
  { split; try apply Theorem113; apply Theorem33 in H0; Ens. }
  destruct H3; apply Theorem100 in H2; auto; clear H4.
  destruct H2 as [f H2], H2, H4; unfold Order_PXY in H4.
  destruct H4, H6, H7, H8; apply Theorem96 in H7; destruct H7.
  unfold Function1_1 in H7; destruct H7 as [H11 H7]; clear H11.
  generalize (Property_F11 f); intros; destruct H11.
  assert (forall u, u ∈ x -> f[u] ≼ u).
  { intros; rewrite <- H5 in H13; double H13.
    apply Property_Value in H14; auto; apply Property_ran in H14.
    assert (Ordinal u /\ Ordinal f[u]).
    { rewrite H5 in H13; apply H0 in H13.
      add (u ∈ y) H1; apply Theorem111 in H1.
      unfold Section in H9; destruct H9; apply H9 in H14.
      unfold R in H14; apply AxiomII in H14; destruct H14; auto. }
    apply Theorem110 in H15; AssE ([u,f[u]]); try apply Theorem49; Ens.
    assert (Section ran(f) E R /\ Order_Pr f⁻¹ E E /\ On f⁻¹ ran(f) /\ To f⁻¹ R).
    { split; auto; split; auto; split; try (split; auto).
      rewrite H12, H5; unfold Included; intros.
      apply H0 in H17; add (z ∈ y) H1; apply Theorem111 in H1.
      unfold R; apply AxiomII; split; Ens. }
    apply Theorem94 with (u:= f[u]) in H17; auto; rewrite <- H12 in H13.
    apply Lemma96''' in H13; try rewrite (Theorem61 f) in *; auto.
    rewrite <- H13 in H17; unfold LessEqual; destruct H15.
    - unfold Rrelation, E in H17; elim H17.
      apply AxiomII_P; split; auto.
    - destruct H15; try symmetry in H15; tauto. }
  apply Theorem114 in H9; clear H11 H12; double H0.
  try apply Theorem33 in H11; auto; apply Theorem153 in H11.
  assert (x ≈ ran(f)). { unfold Equivalent; exists f; split; split; auto. }
  assert (ran(f) ≼ y /\ Ensemble ran(f)).
  { assert (ran(f) ⊂ y).
    { unfold Included; intros.
      unfold Range in H14; apply AxiomII in H14; destruct H14, H15.
      double H15; apply Property_dom in H16; double H16.
      apply Property_Value in H17; auto; add ([x0,f[x0]] ∈ f) H15.
      unfold Function in H2; apply H2 in H15; rewrite H15 in *.
      clear H15 H17; rewrite H5 in H16; double H16; apply H13 in H16.
      unfold LessEqual in H16; destruct H16.
      - apply H0 in H15; unfold Ordinal in H1; destruct H1.
        unfold full in H17; apply H17 in H15; apply H15 in H16; auto.
      - rewrite H16; apply H0 in H15; auto. }
    split; try apply Theorem33 with (x:= y); auto.
    generalize (classic (ran(f) = y)); intros.
    unfold LessEqual; destruct H15; try tauto.
    apply Theorem108 in H14; auto; unfold Ordinal in H9; apply H9. }
  destruct H14.
  assert (WellOrdered E \{ λ z, x ≈ z /\ Ordinal z \}).
  { assert (\{ λ z, x ≈ z /\ Ordinal z \} ⊂ R).
    { unfold Included; intros; apply AxiomII in H16.
      destruct H16, H17; apply AxiomII; split; auto. }
    apply (Lemma97 _ E _) in H16; auto. }
  unfold WellOrdered in H16; destruct H16 as [H17 H16]; clear H17.
  assert (\{ λ z, x ≈ z /\ Ordinal z \} ⊂ \{ λ z, x ≈ z /\ Ordinal z \}
            /\ \{ λ z, x ≈ z /\ Ordinal z \} ≠ Φ).
  { split; try unfold Included; auto.
    apply Lemma35; exists ran(f); apply AxiomII; split; auto. }
  apply H16 in H17; clear H16; destruct H17; unfold FirstMember in H16.
  destruct H16; apply AxiomII in H16; destruct H16, H18.
  assert (x0 ∈ C).
  { unfold C; apply AxiomII; split; auto.
    unfold Cardinal_Number; split; intros.
    - unfold Ordinal_Number, R; apply AxiomII; Ens.
    - intro; assert (y0 ∈ \{ λ z, x ≈ z /\ Ordinal z \}).
      { unfold R in H20; apply AxiomII in H20; destruct H20.
        apply AxiomII; split; auto; split; auto.
        apply Theorem147 with (y:= x0); auto. }
      apply H17 in H23; elim H23; clear H23.
      unfold Rrelation, E; apply AxiomII_P; unfold Less in H21.
      split; auto; apply Theorem49; Ens. }
  apply Theorem156 in H20; clear H16; destruct H20.
  apply Theorem154 in H18; auto; rewrite H20 in H18; clear H20.
  assert (ran(f)∈ \{ λ z, x ≈ z /\ Ordinal z \}). { apply AxiomII; Ens. }
  apply H17 in H20; clear H17; rewrite H18; unfold LessEqual.
  add (Ordinal x0) H9; apply Theorem110 in H9; destruct H9 as [H9|[H9|H9]].
  - elim H20; unfold Rrelation, E; apply AxiomII_P.
    split; try apply Theorem49; Ens.
  - destruct H14.
    + unfold Ordinal in H1; destruct H1.
      unfold full in H17; apply H17 in H14; clear H17.
      unfold Included in H14; apply H14 in H9; auto.
    + rewrite H14 in H9; auto.
  - destruct H14; rewrite H9 in H14; auto.
Qed.

Hint Resolve Theorem157 : set.


(* 定理158 如果y∈R且x⊂y，则P[x]≼P[y] *)

Theorem Theorem158 : forall x y,
  Ensemble y /\ x ⊂ y -> P[x] ≼ P[y].
Proof.
  intros; destruct H.
  assert (Ensemble x). { apply Theorem33 in H0; auto. }
  double H; apply Theorem153 in H2.
  apply Theorem146 in H2; unfold Equivalent in H2.
  destruct H2 as [f H2], H2, H3; double H.
  apply Property_PClass in H5; unfold C in H5.
  apply AxiomII in H5; destruct H5; unfold Cardinal_Number in H6.
  destruct H6; clear H7; unfold Ordinal_Number in H6.
  assert (ran(f|x) ⊂ P[y]).
  { rewrite <- H4; unfold Included; intros.
    unfold Range in H7; apply AxiomII in H7; destruct H7, H8.
    unfold Restriction in H8; apply Theorem4' in H8; destruct H8.
    apply Property_ran in H8; auto. }
  add (ran(f|x) ⊂ P [y]) H6; apply Theorem157 in H6.
  assert (x ≈ ran(f|x)).
  { unfold Function1_1 in H2; destruct H2.
    unfold Equivalent; exists (f|x); split.
    - unfold Function1_1; split.
      + unfold Function; split; intros.
        * unfold Relation; intros; unfold Restriction in H9.
          apply Theorem4' in H9; destruct H9; PP H10 a b; Ens.
        * destruct H9; unfold Restriction in H9, H10.
          apply Theorem4' in H9; apply Theorem4' in H10.
          destruct H9, H10; add ([x0,z] ∈ f) H9.
          unfold Function in H2; apply H2 in H9; auto.
      + unfold Function; split; intros.
        * unfold Relation; intros; PP H9 a b; Ens.
        * destruct H9; unfold Inverse in H9, H10.
          apply AxiomII_P in H9; apply AxiomII_P in H10.
          destruct H9, H10; unfold Restriction in H11, H12.
          apply Theorem4' in H11; apply Theorem4' in H12.
          destruct H11, H12; clear H13 H14.
          assert ([x0,y0] ∈ f⁻¹ /\ [x0,z] ∈ f⁻¹).
          { unfold Inverse; split; apply AxiomII_P; Ens. }
          unfold Function in H8; apply H8 in H13; auto.
    - split; auto; apply AxiomI; intros; split; intros.
      + unfold Domain in H9; apply AxiomII in H9; destruct H9, H10.
        unfold Restriction in H10; apply Theorem4' in H10; destruct H10.
        unfold Cartesian in H11; apply AxiomII_P in H11; apply H11.
      + unfold Domain; apply AxiomII; split; Ens.
        double H9; unfold Included in H0; apply H0 in H10.
        rewrite <- H3 in H10; apply Property_Value in H10; auto.
        exists f[z]; unfold Restriction; apply Theorem4'; split; auto.
        unfold Cartesian; apply AxiomII_P; repeat split; Ens.
        AssE [z,f[z]]; apply Theorem49 in H11; destruct H11.
        apply Theorem19; auto. }
  assert (Ensemble ran(f|x)). { apply Theorem33 in H7; auto. }
  apply Theorem154 in H8; auto; rewrite <- H8 in H6; auto.
Qed.

Hint Resolve Theorem158 : set.


(* 定理159 如果x与y均为集，u⊂x，v⊂y，x≈v且y≈u，则x≈y *)

Theorem Theorem159 : forall (x y: Class),
  Ensemble x /\ Ensemble y ->
  (forall u v, u ⊂ x /\ v ⊂ y -> x ≈ v /\ y ≈ u -> x ≈ y).
Proof.
  intros; destruct H0, H1; elim H; intros.
  assert (Ensemble x /\ Ensemble v).
  { split; apply Theorem33 in H2; auto. }
  assert (Ensemble y /\ Ensemble u).
  { split; apply Theorem33 in H0; auto. }
  apply Theorem154 in H; apply Theorem154 in H6.
  apply Theorem154 in H7; apply H; apply H6 in H1.
  apply H7 in H3; clear H H6 H7; double H4; double H5.
  add (u ⊂ x) H4; add (v ⊂ y) H6; clear H0 H2.
  apply Theorem158 in H4; apply Theorem158 in H6.
  rewrite <- H3 in H4; rewrite <- H1 in H6; clear H1 H3.
  apply Property_PClass in H; apply Property_PClass in H5.
  unfold C in H, H5; apply AxiomII in H; apply AxiomII in H5.
  destruct H, H5; unfold Cardinal_Number in H0, H2.
  destruct H0, H2; unfold Ordinal_Number, R in H0, H2.
  apply AxiomII in H0; apply AxiomII in H2; destruct H0, H2.
  clear H H0 H1 H2 H3 H5.
  assert (Ordinal P [x] /\ Ordinal P [y]). { auto. }
  assert (Ordinal P [y] /\ Ordinal P [x]). { auto. }
  apply Theorem118 in H; apply Theorem118 in H0; clear H7 H8.
  apply H in H6; apply H0 in H4; clear H H0.
  apply Theorem27; split; auto.
Qed.

Hint Resolve Theorem159 : set.


(* 定理160 如果f是一个函数同时f是一个集，则P(f的值域)≼P(f的定义域) *)

Definition En_g f c : Class :=
  \{\ λ v u, v ∈ ran(f) /\ u = c[\{ λ x, v = f[x] \}] \}\.

Lemma Lemma160 : forall c f y,
  Function f -> Ensemble dom(f) -> ChoiceFunction c -> dom( c) = μ ~ [Φ] ->
  y ∈ ran( f) -> \{ λ x, y = f[x] \} ∈ dom(c).
Proof.
  intros.
  unfold ChoiceFunction in H1; destruct H1.
  unfold Range in H3; apply AxiomII in H3; destruct H3, H5.
  rewrite H2; unfold Setminus; apply Theorem4'.
  assert (Ensemble (\{ λ x, y = f[x] \})).
  { apply Theorem33 with (x:= dom(f)); auto.
    unfold Included; intros; apply AxiomII in H6; destruct H6.
    rewrite H7 in H5; clear H7; apply Property_ran in H5.
    apply Property_Value' in H5; auto; apply Property_dom in H5; auto. }
  split; try apply Theorem19; auto.
  unfold Complement; apply AxiomII; split; auto.
  unfold NotIn; intro; unfold Singleton in H7.
  apply AxiomII in H7; clear H6; destruct H7.
  assert (Φ ∈ μ).
  { apply Theorem19; generalize AxiomVIII; intros.
    destruct H8; Ens; exists x0; apply H8. }
  apply H7 in H8; clear H7.
  assert (x ∈ \{ λ x, y = f [x] \}).
  { apply AxiomII; double H5; apply Property_dom in H7.
    split; Ens; apply Property_Value in H7; auto.
    unfold Function in H; apply H with (x:=x); Ens. }
  rewrite H8 in H7; generalize (Theorem16 x); intros; contradiction.
Qed.

Theorem Theorem160 : forall f,
  Function f -> P[ran(f)] ≼ P[dom(f)].
Proof.
  intros.
  generalize (classic (Ensemble dom(f))); intros; destruct H0.
  - generalize AxiomIX; intros; destruct H1 as [c H1], H1.
    assert (Function1_1 (En_g f c)).
    { unfold Function1_1, Function; repeat split; intros.
      - unfold Relation; intros; PP H3 a b; Ens.
      - unfold En_g in H3; destruct H3.
        apply AxiomII_P in H3; apply AxiomII_P in H4.
        destruct H3, H4, H5, H6; rewrite H7, H8; auto.
      - unfold Relation; intros; PP H3 a b; Ens.
      - unfold Inverse, En_g in H3; destruct H3.
        apply AxiomII_P in H3; apply AxiomII_P in H4.
        destruct H3, H4; clear H3 H4; apply AxiomII_P in H5.
        apply AxiomII_P in H6; destruct H5, H6, H4, H6.
        assert (\{ λ x, y=f[x] \} ∈ dom(c) /\ \{ λ x, z=f[x] \} ∈ dom(c)).
        { split; apply Lemma160; auto. }
        destruct H9; apply H1 in H9; apply H1 in H10.
        rewrite <- H7 in H9; rewrite <- H8 in H10; apply AxiomII in H9.
        apply AxiomII in H10; destruct H9, H10; rewrite H11, H12; auto. }
    assert (ran(En_g f c) ⊂ dom(f)).
    { unfold Included; intros; unfold Range, En_g in H4; unfold Domain.
      apply AxiomII in H4; destruct H4, H5; apply AxiomII_P in H5.
      destruct H5, H6; apply AxiomII; split; auto; exists f[z].
      assert (\{ λ x0, x = f [x0] \} ∈ dom(c)). { apply Lemma160; auto. }
      apply H1 in H8; rewrite <- H7 in H8; apply AxiomII in H8; destruct H8.
      rewrite H9 in H6; clear H9; apply Property_Value'; auto. }
    assert (Ensemble dom(f) /\ ran(En_g f c) ⊂ dom(f)); auto.
    apply Theorem158 in H5; auto.
    assert (dom(En_g f c) ≈ ran(En_g f c)).
    { unfold Equivalent; exists (En_g f c); auto. }
    assert (dom(En_g f c) = ran(f)).
    { apply AxiomI; split; intros.
      - unfold Domain, En_g in H7; apply AxiomII in H7.
        destruct H7, H8; apply AxiomII_P in H8; apply H8.
      - unfold Domain, En_g; apply AxiomII; split; Ens.
        exists c[\{ λ x, z = f [x] \}]; apply AxiomII_P; split; auto.
        apply Theorem49; split; Ens; exists \{ λ x, z = f [x] \}.
        unfold ChoiceFunction in H1; apply H1; apply Lemma160; auto. }
    rewrite H7 in H6; clear H7.
    assert (Ensemble ran(f) /\ Ensemble ran(En_g f c)).
    { double H0; split; try apply AxiomV in H0; auto.
      apply Theorem33 with (x:= dom(f)); auto. }
    apply Theorem154 in H7; apply H7 in H6; clear H7; rewrite H6; auto.
  - generalize Theorem152; intros; destruct H1, H2.
    generalize (classic (dom(f) ∈ dom(P))); intros; destruct H4.
    + rewrite H2 in H4; apply Theorem19 in H4; contradiction.
    + apply Theorem69 in H4; rewrite H4; clear H4.
      generalize (classic (ran(f) ∈ dom(P))); intros; destruct H4.
      * rewrite H2 in H4; apply Theorem19 in H4.
        apply Property_PClass in H4; unfold LessEqual.
        left; apply Theorem19; Ens.
      * apply Theorem69 in H4; rewrite H4; unfold LessEqual; tauto.
Qed.

Hint Resolve Theorem160 : set.


(* 定理161 如果x是一个集，则P[x] ≺ P[pow(x)] *)

Theorem Theorem161 : forall x,
  Ensemble x -> P[x] ≺ P[ pow(x) ].
Proof.
  intros.
  assert (x ≈ \{ λ v, exists u, u∈x /\ v = [u] \}).
  { unfold Equivalent; exists \{\ λ u v, u∈x /\ v = [u] \}\.
    repeat split; auto; unfold Relation; intros; try PP H0 a b; Ens.
    - destruct H0; apply AxiomII_P in H0; apply AxiomII_P in H1.
      destruct H0, H1, H2, H3; rewrite H4, H5; auto.
    - destruct H0; apply AxiomII_P in H0; apply AxiomII_P in H1.
      destruct H0, H1; apply AxiomII_P in H2; apply AxiomII_P in H3.
      clear H0 H1; destruct H2, H3, H1, H3; rewrite H4 in H5.
      assert (y∈[y]). { apply AxiomII; split; Ens. }
      rewrite H5 in H6; apply AxiomII in H6; destruct H6.
      apply H7; apply Theorem19; Ens.
    - apply AxiomI; split; intros.
      + unfold Domain in H0; apply AxiomII in H0; destruct H0, H1.
        apply AxiomII_P in H1; apply H1.
      + unfold Domain; apply AxiomII; split; Ens; exists [z].
        AssE z; apply Theorem42 in H1; apply AxiomII_P.
        repeat split; try apply Theorem49; Ens.
    - apply AxiomI; split; intros.
      + unfold Range in H0; apply AxiomII in H0; destruct H0, H1.
        apply AxiomII_P in H1; destruct H1, H2; apply AxiomII; Ens.
      + apply AxiomII in H0; destruct H0, H1, H1; unfold Range.
        apply AxiomII; split; auto; exists x0; apply AxiomII_P.
        repeat split; try apply Theorem49; Ens. }
  assert (Ensemble pow(x) /\ \{λ v, exists u, u∈x /\ v=[u]\} ⊂ pow(x)).
  { split; try apply Theorem38 in H; auto.
    unfold Included; intros; apply AxiomII in H1; destruct H1, H2, H2.
    rewrite H3 in *; clear H3; unfold PowerSet; apply AxiomII; split; auto.
    unfold Included; intros; apply AxiomII in H3; destruct H3.
    rewrite H4; try apply Theorem19; Ens. }
  assert (Ensemble x /\ Ensemble \{λ v, exists u, u∈x /\ v=[u]\}).
  { split; auto; destruct H1; apply Theorem33 in H2; auto. }
  apply Theorem158 in H1; apply Theorem154 in H2; apply H2 in H0.
  rewrite <- H0 in H1; clear H0 H2; unfold LessEqual in H1.
  unfold Less; destruct H1; auto.
  assert (Ensemble x /\ Ensemble pow(x)).
  { split; auto; apply Theorem38 in H; auto. }
  apply Theorem154 in H1; apply H1 in H0; clear H1.
  unfold Equivalent in H0; destruct H0 as [f H0], H0, H1.
  assert (\{λ v, v ∈ x /\ v ∉ f[v]\} ∈ ran(f)).
  { assert (\{λ v, v ∈ x /\ v ∉ f[v]\} ⊂ x).
    { unfold Included; intros; apply AxiomII in H3; apply H3. }
    double H3; apply Theorem33 in H4; auto; rewrite H2.
    unfold PowerSet; apply AxiomII; split; auto. }
  unfold Range in H3; apply AxiomII in H3; destruct H3, H4 as [u H4].
  double H4; apply Property_dom in H5; unfold Function1_1 in H0.
  destruct H0; clear H6; double H5; apply Property_Value in H6; auto.
  rewrite H1 in H5; add ([u,f[u]] ∈ f) H4; apply H0 in H4; clear H6.
  generalize (classic (u ∈ f[u])); intros; destruct H6.
  - double H6; rewrite <- H4 in H7; apply AxiomII in H7.
    destruct H7, H8; contradiction.
  - elim H6; rewrite <- H4; apply AxiomII; Ens.
Qed.

Hint Resolve Theorem161 : set.


(* 定理162 C不是一个集 *)

Theorem Theorem162 : ~ Ensemble C.
Proof.
  intro.
  apply AxiomVI in H; double H.
  apply Theorem38 in H0; try apply C.
  apply Property_PClass in H0.
  assert (Ensemble (∪C) /\ P[ pow( ∪C ) ] ⊂ ∪C).
  { split; auto; apply Theorem32 in H0; apply H0. }
  apply Theorem158 in H1; rewrite Theorem155 in H1.
  double H; apply Theorem161 in H2; unfold Less in H2.
  unfold LessEqual in H1; destruct H1.
  - apply Property_PClass in H; generalize Theorem150; intros.
    apply Theorem88 in H3; destruct H3; unfold Asymmetric in H4.
    assert (P[∪C] ∈ C /\ P[pow(∪C)] ∈ C /\ Rrelation P[∪C] E P[pow(∪C)]).
    { repeat split; auto; unfold Rrelation, E.
      apply AxiomII_P; split; try apply Theorem49; Ens. }
    apply H4 in H5; apply H5; clear H4 H5.
    unfold Rrelation, E; apply AxiomII_P.
    split; try apply Theorem49; Ens.
  - rewrite H1 in H2.
    generalize (Theorem101 P[∪C]); intros; contradiction.
Qed.

Hint Resolve Theorem162 : set.


(* 我们把基数分为两类，有限基数与无限基数 *)


(* 有限基数 *)

(* 定理163 如果x∈w，y∈w且x+1≈y+1，则x≈y *)

Ltac SplitEns := apply AxiomII; split; Ens.

Ltac SplitEnsP := apply AxiomII_P; split; try apply Theorem49; Ens.

Definition En_g' f x y : Class :=
  \{\ λ u v, [u,v] ∈ (f ~ ([[x,f[x]]] ∪ [[f⁻¹[y],y]])) \/
      [u,v] = [f⁻¹[y],f[x]] \/ [u,v] = [x,y] \}\.

Theorem Theorem163 : forall x y,
  x∈W -> y∈W -> (PlusOne x) ≈ (PlusOne y) -> x ≈ y.
Proof.
  intros.
  unfold Equivalent in H1; destruct H1 as [f H1], H1, H2.
  unfold Function1_1 in H1; destruct H1; unfold Equivalent.
  exists ((En_g' f x y) | x); repeat split; intros.
  - unfold Relation; intros; unfold Restriction in H5.
    apply Theorem4' in H5; destruct H5; PP H6 a b; Ens.
  - destruct H5; unfold Restriction in H5, H6.
    apply Theorem4' in H5; apply Theorem4' in H6.
    destruct H5, H6; clear H8; unfold En_g' in H5, H6.
    apply AxiomII_P in H5; apply AxiomII_P in H6; destruct H5,H6.
    unfold Cartesian in H7; apply AxiomII_P in H7; clear H5.
    destruct H7, H7; clear H10; destruct H8, H9.
    + unfold Setminus in H8, H9; apply Theorem4' in H8.
      apply Theorem4' in H9; destruct H8, H9; clear H10 H11.
      unfold Function in H1; apply H1 with (x:= x0); auto.
    + destruct H9.
      * unfold Setminus in H8; apply Theorem4' in H8; destruct H8.
        unfold Complement in H10; apply AxiomII in H10; clear H5.
        destruct H10; elim H10; clear H10; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H10.
        apply Theorem49 in H6; apply Theorem55 in H9; auto.
        destruct H9; clear H10; double H8; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H8.
        apply H1 in H8; clear H10; rewrite H9 in H8.
        rewrite <- Lemma96''' in H8; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply Theorem4; right.
        unfold Singleton; apply AxiomII; split; Ens.
      * apply Theorem49 in H6; apply Theorem55 in H9; auto; destruct H9.
        rewrite H9 in H7; generalize (Theorem101 x); contradiction.
    + destruct H8.
      * unfold Setminus in H9; apply Theorem4' in H9; destruct H9.
        unfold Complement in H10; apply AxiomII in H10; clear H6.
        destruct H10; elim H10; clear H10; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H10.
        apply Theorem49 in H5; apply Theorem55 in H8; auto.
        destruct H8; clear H10; double H9; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H9.
        apply H1 in H9; clear H10; rewrite H8 in H9.
        rewrite <- Lemma96''' in H9; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply Theorem4; right.
        unfold Singleton; apply AxiomII; split; Ens.
      * apply Theorem49 in H5; apply Theorem55 in H8; auto; destruct H8.
        rewrite H8 in H7; generalize (Theorem101 x); contradiction.
    + apply Theorem49 in H5; apply Theorem49 in H6.
      destruct H8, H9; apply Theorem55 in H8; apply Theorem55 in H9; auto.
      * destruct H8, H9; rewrite H10, H11; auto.
      * destruct H9; rewrite H9 in H7.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H8; rewrite H8 in H7.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H8; rewrite H8 in H7.
        generalize (Theorem101 x); intros; contradiction.
  - unfold Relation; intros; PP H5 a b; Ens.
  - destruct H5; unfold Inverse, Restriction in H5, H6.
    apply AxiomII_P in H5; apply AxiomII_P in H6; destruct H5, H6.
    apply Theorem4' in H7; apply Theorem4' in H8; destruct H7, H8.
    apply AxiomII_P in H7; apply AxiomII_P in H8; destruct H7, H8.
    unfold Cartesian in H9; apply AxiomII_P in H9; clear H7.
    destruct H9, H9; clear H13; apply AxiomII_P in H10; clear H8.
    destruct H10, H10; clear H13; destruct H11, H12.
    + unfold Setminus in H11, H12; apply Theorem4' in H11.
      apply Theorem4' in H12; destruct H11, H12; clear H13 H14.
      assert ([x0,y0] ∈ f⁻¹ /\ [x0,z] ∈ f⁻¹).
      { unfold Inverse; split; apply AxiomII_P; split; auto. }
      unfold Function in H4; apply H4 in H13; auto.
    + destruct H12.
      * unfold Setminus in H11; apply Theorem4' in H11; destruct H11.
        clear H13; apply Theorem49 in H8; apply Theorem55 in H12; auto.
        destruct H12; rewrite H13 in *; double H11.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],y0] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply AxiomII_P; split; auto; AssE [x,f[x]].
          apply Theorem49 in H15; destruct H15; apply Theorem49; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H9; generalize (Theorem101 x); contradiction.
      * unfold Setminus in H11; apply Theorem4' in H11; destruct H11.
        unfold Complement in H13; apply AxiomII in H13; clear H7.
        destruct H13; elim H13; clear H13; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H13.
        apply Theorem49 in H8; apply Theorem55 in H12; auto.
        destruct H12; rewrite H13 in *; clear H6 H8 H12 H13.
        assert ([y,y0] ∈ f⁻¹). { apply AxiomII_P; Ens. }
        double H6; apply Property_dom in H8; apply Property_Value in H8; auto.
        add ([y,y0] ∈ f⁻¹) H8; apply H4 in H8; rewrite H8; auto.
    + destruct H11.
      * unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
        clear H13; apply Theorem49 in H7; apply Theorem55 in H11; auto.
        destruct H11; rewrite H13 in *; double H12.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],z] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply AxiomII_P; split; auto; AssE [x,f[x]].
          apply Theorem49 in H15; destruct H15; apply Theorem49; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H10; generalize (Theorem101 x); contradiction.
      * unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
        unfold Complement in H13; apply AxiomII in H13; clear H8.
        destruct H13; elim H13; clear H13; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H13.
        apply Theorem49 in H7; apply Theorem55 in H11; auto.
        destruct H11; rewrite H13 in *; clear H5 H7 H11 H13.
        assert ([y,z] ∈ f⁻¹). { apply AxiomII_P; Ens. }
        double H5; apply Property_dom in H7; apply Property_Value in H7; auto.
        add ([y,z] ∈ f⁻¹) H7; apply H4 in H7; rewrite H7; auto.
    + apply Theorem49 in H7; apply Theorem49 in H8.
      destruct H11, H12; apply Theorem55 in H11; apply Theorem55 in H12; auto.
      * destruct H11, H12; rewrite H11, H12; auto.
      * destruct H12; rewrite H12 in H10.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H11; rewrite H11 in H9.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H12; rewrite H12 in H10.
        generalize (Theorem101 x); intros; contradiction.
  - apply AxiomI; split; intros.
    + unfold Domain in H5; apply AxiomII in H5; destruct H5, H6.
      unfold Restriction in H6; apply Theorem4' in H6; destruct H6.
      unfold Cartesian in H7; apply AxiomII_P in H7; apply H7.
    + unfold Domain; apply AxiomII; split; Ens.
      assert ([x,f[x]] ∈ f).
      { apply Property_Value; auto; rewrite H2; unfold PlusOne.
        apply Theorem4; right; apply AxiomII; split; Ens. }
      generalize (classic (z = f⁻¹[y])); intros; destruct H7.
      * rewrite H7 in *; AssE [x,f[x]]; clear H6 H7.
        apply Theorem49 in H8; destruct H8.
        exists f[x]; unfold Restriction; apply Theorem4'.
        split; SplitEnsP; split; try apply Theorem19; auto.
      * assert (z ∈ dom(f)). { rewrite H2; apply Theorem4; tauto. }
        apply Property_Value in H8; auto; AssE [z,f[z]].
        apply Theorem49 in H9; destruct H9; exists f[z].
        unfold Restriction; apply Theorem4'; split; SplitEnsP.
        { left; unfold Setminus; apply Theorem4'; split; auto.
          unfold Complement; apply AxiomII; split; Ens.
          intro; apply Theorem4 in H11; destruct H11.
          - apply AxiomII in H11; destruct H11; clear H11.
            assert ([x,f[x]] ∈ μ). { apply Theorem19; Ens. }
            apply H12 in H11; clear H12; apply Theorem55 in H11; auto.
            destruct H11; rewrite H11 in H5; generalize (Theorem101 x); auto.
          - apply AxiomII in H11; destruct H11; clear H11.
            assert ([(f⁻¹)[y],y] ∈ μ).
            { apply Theorem19; Ens; exists f.
              assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply Theorem4; right.
                apply AxiomII; split; Ens. }
              rewrite Lemma96' in H11; apply Property_Value in H11; auto.
              apply AxiomII_P in H11; apply H11. }
            apply H12 in H11; clear H12; apply Theorem55 in H11; auto.
            destruct H11; contradiction. }
        { split; try apply Theorem19; auto. }
  - apply AxiomI; split; intros.
    + unfold Range in H5; apply AxiomII in H5; destruct H5, H6.
      unfold Restriction in H6; apply Theorem4' in H6; destruct H6.
      unfold Cartesian in H7; apply AxiomII_P in H7; destruct H7.
      clear H7; destruct H8; clear H8; unfold En_g' in H6.
      apply AxiomII_P in H6; destruct H6, H8 as [H8|[H8|H8]].
      * unfold Setminus in H8; apply Theorem4' in H8; destruct H8.
        unfold Complement in H9; apply AxiomII in H9; clear H6.
        destruct H9; double H8; apply Property_ran in H10; rewrite H3 in H10.
        unfold PlusOne in H10; apply Theorem4 in H10; destruct H10; auto.
        apply AxiomII in H10; clear H5; destruct H10.
        rewrite H10 in *; try apply Theorem19; Ens; clear H10.
        double H8; apply Property_ran in H10; rewrite Lemma96' in H10.
        apply Property_Value in H10; auto; apply Theorem49 in H6.
        destruct H6; clear H11; add ([y,x0] ∈ f⁻¹) H10; try SplitEnsP.
        apply H4 in H10; rewrite H10 in H9; elim H9.
        apply Theorem4; right; SplitEns.
      * apply Theorem49 in H6; apply Theorem55 in H8; auto; destruct H8.
        assert (x ∈ dom(f)).
        { rewrite H2; unfold PlusOne; apply Theorem4; right.
          unfold Singleton; apply AxiomII; split; Ens. }
        double H10; apply Property_Value in H11; auto.
        apply Property_ran in H11; rewrite H3 in H11; unfold PlusOne in H11.
        apply Theorem4 in H11; rewrite H9 in *; destruct H11; auto.
        apply AxiomII in H11; clear H5; destruct H11.
        rewrite <- H11 in H8; try apply Theorem19; Ens.
        pattern f at 2 in H8; rewrite <- Theorem61 in H8.
        rewrite <- Lemma96''' in H8; try rewrite Theorem61; auto.
        { rewrite H8 in H7; generalize (Theorem101 x); contradiction. }
        { rewrite <- Lemma96; auto. }
      * apply Theorem49 in H6; apply Theorem55 in H8; auto; destruct H8.
        rewrite H8 in H7; generalize (Theorem101 x); contradiction. 
    + unfold Range; apply AxiomII; split; Ens.
      assert (z∈ran(f)). { rewrite H3; unfold PlusOne; apply Theorem4; auto. }
      generalize (classic (z = f[x])); intros; destruct H7.
      * rewrite H7 in *; clear H7.
        assert (y ∈ ran(f)).
        { rewrite H3; unfold PlusOne; apply Theorem4; right.
          unfold Singleton; apply AxiomII; split; Ens. }
        double H7; rewrite Lemma96' in H8; apply Property_Value in H8; auto.
        apply Property_ran in H8; rewrite <- Lemma96 in H8; rewrite H2 in H8.
        unfold PlusOne in H8; apply Theorem4 in H8; destruct H8.
        { exists (f⁻¹)[y]; unfold Restriction; apply Theorem4'.
          split; SplitEnsP; split; try apply Theorem19; Ens. }
        { unfold Singleton in H8; apply AxiomII in H8; destruct H8.
          rewrite <- H9 in H5; try apply Theorem19; Ens.
          rewrite <- Lemma96''' in H5; auto.
          generalize (Theorem101 y); intros; contradiction. }
      * unfold Range in H6; apply AxiomII in H6; destruct H6, H8; exists x0.
        AssE [x0,z]; unfold Restriction; apply Theorem4'; split.
        { unfold En_g'; apply AxiomII_P; split; auto; left.
          unfold Setminus; apply Theorem4'; split; auto; unfold Complement.
          apply AxiomII; split; auto; intro; apply Theorem4 in H10.
          destruct H10; apply AxiomII in H10; destruct H10.
          - assert ([x,f[x]] ∈ μ); clear H10.
            { apply Theorem19; Ens; exists f; apply Property_Value; auto.
              rewrite H2; unfold PlusOne; apply Theorem4; right.
              unfold Singleton; apply AxiomII; split; Ens. }
            apply H11 in H12; clear H11; apply Theorem49 in H9.
            apply Theorem55 in H12; auto; destruct H12; tauto.
          - assert ([(f⁻¹)[y], y] ∈ μ); clear H10.
            { apply Theorem19; Ens; exists f. assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply Theorem4; right.
                apply AxiomII; split; Ens. }
              rewrite Lemma96' in H10; apply Property_Value in H10; auto.
              apply AxiomII_P in H10; apply H10. }
            apply H11 in H12; clear H11; apply Theorem49 in H9.
            apply Theorem55 in H12; auto; destruct H12; rewrite H11 in H5.
            generalize (Theorem101 y); intros; contradiction. }
        { double H8; apply Property_dom in H10; rewrite H2 in H10.
          unfold PlusOne in H10; apply Theorem4 in H10; unfold Cartesian.
          apply AxiomII_P; repeat split; auto; try apply Theorem19; Ens.
          destruct H10; auto; apply AxiomII in H10; destruct H10.
          rewrite H11 in H8; try apply Theorem19; Ens; double H8.
          apply Property_dom in H12; apply Property_Value in H12; auto.
          add ([x,z] ∈ f) H12; apply H1 in H12; symmetry in H12; tauto. }
Qed.

Hint Resolve Theorem163 : set.


(* 定理164 w⊂C *)

Theorem Theorem164 : W ⊂ C.
Proof.
  intros.
  unfold Included; apply Mathematical_Induction.
  - assert (Φ ∈ W); try apply Theorem135; try apply W.
    unfold W in H; apply AxiomII in H; destruct H; unfold Integer in H0.
    destruct H0; unfold C; apply AxiomII.
    unfold Cardinal_Number, Ordinal_Number; repeat split; intros; auto.
    + unfold R; apply AxiomII; split; auto.
    + unfold Less in H3; generalize (Theorem16 y); contradiction.
  - intros; destruct H; double H; apply Theorem134 in H1; unfold W in H1.
    apply AxiomII in H1; unfold Integer in H1; destruct H1, H2.
    unfold C in H0; apply AxiomII in H0; destruct H0.
    unfold Cardinal_Number, Ordinal_Number in H4; destruct H4.
    unfold C; apply AxiomII; split; auto; split; intros.
    + unfold Ordinal_Number, R; apply AxiomII; split; auto.
    + unfold Less, PlusOne in H7; apply Theorem4 in H7; destruct H7.
      * assert (y ∈ W).
        { unfold W; apply AxiomII; split; Ens.
          unfold W in H; apply AxiomII in H; destruct H.
          apply Theorem132 in H7; auto. }
        intro; clear H6; double H8; apply AxiomII in H6; destruct H6.
        unfold Integer in H10; destruct H10; unfold WellOrdered in H11.
        destruct H11 as [H12 H11]; clear H12.
        generalize (classic (y = Φ)); intros; destruct H12.
        { rewrite H12 in H9; clear H12; unfold Equivalent in H9.
          destruct H9 as [f H9]; destruct H9, H12.
          assert (k ∈ (PlusOne k)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply AxiomII; split; Ens. }
          rewrite <- H12 in H14; unfold Function1_1 in H9; destruct H9.
          apply Property_Value in H14; auto; apply Property_ran in H14.
          rewrite H13 in H14; generalize (Theorem16 f[k]); contradiction. }
        { assert (y ⊂ y /\ y ≠ Φ). { split; unfold Included; Ens. }
          apply H11 in H13; clear H11 H12; destruct H13.
          assert (y = PlusOne x).
          { apply Theorem133; split; auto; try apply AxiomII; Ens. }
          unfold FirstMember in H11; destruct H11; clear H13.
          rewrite H12 in H9; apply Theorem163 in H9; auto.
          - assert (x ∈ R /\ x ≺ k).
            { unfold Less; split.
              - unfold R; apply AxiomII; split; Ens.
                apply Theorem111 with (x:= y); auto.
              - unfold R in H4; apply AxiomII in H4; destruct H4.
                unfold Ordinal, full in H13; destruct H13.
                apply H14 in H7; apply H7 in H11; auto. }
            destruct H13; apply H5 in H14; auto.
          - generalize Property_W; intros; unfold Ordinal, full in H13.
            destruct H13; apply H14 in H8; apply H8 in H11; auto. }
      * unfold Singleton in H7; apply AxiomII in H7; destruct H7.
        assert (k ∈ μ); try apply Theorem19; Ens; apply H8 in H9.
        clear H6 H7 H8; rewrite H9; intro; clear H9; double H.
        apply AxiomII in H7; clear H0; destruct H7; unfold Integer in H7.
        destruct H7; unfold WellOrdered in H8; destruct H8; clear H8.
        generalize (classic (k = Φ)); intros; destruct H8.
        { rewrite H8 in H6; clear H8; unfold Equivalent in H6.
          destruct H6 as [f H6]; destruct H6, H8.
          assert (Φ ∈ (PlusOne Φ)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply AxiomII; split; auto; generalize AxiomVIII; intros.
            destruct H11, H11, H12; Ens. }
          rewrite <- H8 in H11; unfold Function1_1 in H6; destruct H6.
          apply Property_Value in H11; auto; apply Property_ran in H11.
          rewrite H10 in H11; generalize (Theorem16 f[Φ]); contradiction. }
        { assert (k ⊂ k /\ k ≠ Φ). { split; unfold Included; Ens. }
          apply H9 in H10; clear H8 H9; destruct H10.
          assert (k = PlusOne x).
          { apply Theorem133; split; auto; try apply AxiomII; Ens. }
          unfold FirstMember in H8; destruct H8; clear H10.
          pattern k at 2 in H6; rewrite H9 in H6; apply Theorem163 in H6; auto.
          - apply H5 in H8; try contradiction; unfold R; apply AxiomII.
            split; Ens; apply Theorem111 with (x:= k); auto.
          - unfold W; apply AxiomII; split; Ens.
            apply AxiomII in H; destruct H; apply Theorem132 in H8; auto. }
Qed.

Hint Resolve Theorem164 : set.


(* 定理165 w∈C *)

Theorem Theorem165 : W ∈ C.
Proof.
  generalize Theorem138; intros; AssE W.
  unfold C; apply AxiomII; split; auto.
  unfold Cardinal_Number; split; intros.
  - unfold Ordinal_Number; auto.
  - unfold Less in H2; intro; double H2.
    apply Theorem134 in H4.
    assert (Ensemble (PlusOne y) /\ y ⊂ (PlusOne y)).
    { split; Ens; unfold PlusOne, Included; intros.
      apply Theorem4; tauto. }
    apply Theorem158 in H5.
    assert (Ensemble W /\ (PlusOne y) ⊂ W).
    { split; auto; unfold PlusOne, Included; intros.
      apply Theorem4 in H6; destruct H6.
      - unfold W in H2; apply AxiomII in H2; destruct H2.
        unfold W; apply AxiomII; split; Ens.
        apply Theorem132 in H6; auto.
      - unfold Singleton in H6; apply AxiomII in H6; destruct H6.
        rewrite H7; try apply Theorem19; Ens. }
    apply Theorem158 in H6; apply Theorem154 in H3; Ens.
    unfold LessEqual in H5, H6; destruct H5, H6.
    + generalize (Theorem102 P[y] P[PlusOne y]); intros.
      rewrite H3 in H6; elim H7; split; auto.
    + rewrite H3 in H6; rewrite <- H6 in H5.
      generalize (Theorem101 P[PlusOne y]); intros; contradiction.
    + rewrite H3, H5 in H6.
      generalize (Theorem101 P[PlusOne y]); intros; contradiction.
    + apply Theorem154 in H5; Ens.
      apply Theorem164 in H4; unfold C in H4.
      apply AxiomII in H4; destruct H4; unfold Cardinal_Number in H7.
      destruct H7; apply H8 in H1.
      * elim H1; apply Theorem146; auto.
      * unfold Less, PlusOne; apply Theorem4; right.
        unfold Singleton; apply AxiomII; Ens.
Qed.

Hint Resolve Theorem165 : set.


(* 定义166 x是有限的当且仅当P[x]∈w *)

Definition Finite (x: Class) : Prop := P [x] ∈ W.

Corollary Property_Finite : forall x, Finite x -> Ensemble x.
Proof.
  intros; unfold Finite in H.
  generalize (classic (Ensemble x)); intros; destruct H0; auto.
  generalize Theorem152; intros; destruct H1, H2.
  assert (x ∉ dom(P)).
  { rewrite H2; intro; apply Theorem19 in H4; contradiction. }
  apply Theorem69 in H4; rewrite H4 in H; AssE μ.
  generalize Theorem39; intros; contradiction.
Qed.

Hint Unfold Finite : set.


(* 定理167 x是有限的当且仅当存在r使得r良序x，并且r⁻¹也良序x *)

Lemma Lemma167 : forall r x f,
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
    + left; unfold Rrelation; apply AxiomII_P; split; try apply Theorem49; auto.
    + right; left; apply AxiomII_P; split; try apply Theorem49; auto.
    + right; right; rewrite H in H4; clear H.
      assert ([f[v],u] ∈ f⁻¹ /\ [f[v],v] ∈ f⁻¹).
      { unfold Inverse; split; apply AxiomII_P; split; auto.
        - apply Theorem49; split; apply Property_ran in H4; Ens.
        - apply Theorem49; split; apply Property_ran in H5; Ens. }
      unfold Function in H3; apply H3 in H; auto.
  - assert (ran(f|y) ⊂ P [x] /\ ran(f|y) ≠ Φ).
    { destruct H4; split.
      - unfold Included; intros; unfold Range in H6; apply AxiomII in H6.
        destruct H6, H7; unfold Restriction in H7; apply Theorem4' in H7.
        destruct H7; apply Property_ran in H7; rewrite H2 in H7; auto.
      - apply Lemma35 in H5; destruct H5; double H5; apply H4 in H6.
        rewrite <- H1 in H6; apply Property_Value in H6; auto.
        double H6; apply Property_ran in H7; apply Lemma35.
        exists f[x0]; unfold Range; apply AxiomII; split; Ens.
        exists x0; unfold Restriction; apply Theorem4'; split; auto.
        unfold Cartesian; apply AxiomII_P; repeat split; Ens.
        apply Theorem19; Ens. }
    apply H in H5; unfold FirstMember in H5; destruct H5, H5.
    unfold Range in H5; apply AxiomII in H5; destruct H5, H7.
    unfold Restriction in H7; apply Theorem4' in H7; destruct H7.
    exists x1; unfold FirstMember; split; intros.
    + unfold Cartesian in H8; apply AxiomII_P in H8; apply H8.
    + clear H8; double H9; apply H4 in H9; rewrite <- H1 in H9.
      apply Property_Value in H9; auto.
      assert (f[y0] ∈ ran(f|y)).
      { AssE [y0,f[y0]]; apply Theorem49 in H10; destruct H10.
        unfold Range; apply AxiomII; split; auto.
        exists y0; unfold Restriction; apply Theorem4'; split; auto.
        apply AxiomII_P; repeat split; try apply Theorem49; auto.
        apply Theorem19; auto. }
      apply H6 in H10; clear H6; intro; elim H10; clear H10.
      unfold Rrelation at 1 in H6; apply AxiomII_P in H6; destruct H6.
      double H7; apply Property_dom in H11; apply Property_Value in H11; auto.
      add ([x1,f[x1]] ∈ f) H7; apply H0 in H7; rewrite H7; auto.
Qed.

Theorem Theorem167 : forall x,
  Finite x <-> exists r, WellOrdered r x /\ WellOrdered (r⁻¹) x.
Proof.
  intros; split; intros.
  - double H; unfold Finite in H; apply Property_Finite in H0.
    unfold W in H; apply AxiomII in H; destruct H.
    unfold Integer in H1; destruct H1; apply Theorem107 in H1.
    apply Theorem153 in H0; apply Theorem146 in H0.
    unfold Equivalent in H0; destruct H0 as [f H0], H0, H3.
    exists (\{\ λ u v, Rrelation f[u] E f[v] \}\); split.
    + apply Lemma167; auto.
    + assert (\{\ λ u v, Rrelation f [u] E f [v] \}\⁻¹ =
              \{\ λ u v, Rrelation f [u] E⁻¹ f [v] \}\).
      { apply AxiomI; split; intros.
        - PP H5 a b; apply AxiomII_P; apply AxiomII_P in H6; destruct H6.
          apply AxiomII_P in H7; destruct H7; split; auto.
          unfold Rrelation in H8; unfold Rrelation, Inverse.
          apply AxiomII_P; split; auto; AssE [f[b],f[a]].
          apply Theorem49 in H9; destruct H9; apply Theorem49; auto.
        - PP H5 a b; apply AxiomII_P in H6; destruct H6.
          unfold Rrelation, Inverse in H7; apply AxiomII_P in H7; destruct H7.
          apply Theorem49 in H6; destruct H6; apply AxiomII_P.
          split; try apply Theorem49; auto; apply AxiomII_P.
          split; try apply Theorem49; auto. }
      rewrite H5; apply Lemma167; auto.
  - destruct H as [r H], H; unfold Finite.
    generalize Theorem113; intros; destruct H1; clear H2.
    apply Theorem107 in H1; add (WellOrdered E R) H; clear H1.
    apply Theorem99 in H; destruct H as [f H], H, H1.
    unfold Order_PXY in H1; destruct H1, H3, H4, H5; double H6.
    apply Theorem114 in H7; add (Ordinal W) H7; try apply Property_W.
    apply Theorem110 in H7; destruct H7. (* 分三种情况，后两种情况都是 W ⊂ ran(f) *)
    + destruct H2.
      * assert (P[x] = ran(f)).
        { apply Theorem164 in H7; clear H0; AssE ran(f).
          apply Theorem96 in H4; destruct H4; clear H8.
          assert (dom(f) ≈ ran(f)). { unfold Equivalent; exists f; auto. }
          unfold Function1_1 in H4; destruct H4; rewrite (Lemma96 f), (Lemma96' f) in *.
          apply AxiomV in H0; auto; rewrite H2 in *; double H0.
          apply Theorem153 in H0; apply Property_PClass in H10.
          apply Theorem147 with (z:= dom(f⁻¹)) in H0; auto; clear H2 H8.
          unfold C in H7, H10; apply AxiomII in H7; apply AxiomII in H10.
          destruct H7, H10; clear H2 H8; unfold Cardinal_Number in H7, H10.
          destruct H7, H10; unfold Ordinal_Number in H2, H8; double H2; double H8.
          unfold R in H11, H12; apply AxiomII in H11; apply AxiomII in H12.
          destruct H11, H12; clear H11 H12; add (Ordinal dom(f⁻¹)) H14; clear H13.
          apply Theorem110 in H14; destruct H14 as [H11 | [H11 | H11]]; auto.
          - apply H7 in H11; auto; apply Theorem146 in H0; contradiction.
          - apply H10 in H11; auto; contradiction. }
          rewrite H8; auto.
      * rewrite H2 in H7; add (W ∈ R) H7; try apply Theorem138.
        generalize (Theorem102 R W); intros; contradiction.
    + assert (W ⊂ ran(f)).
      { destruct H7; try (rewrite H7; unfold Included; auto).
        apply Theorem114 in H6; unfold Ordinal, full in H6.
        destruct H6; apply H8 in H7; auto. }
      assert (~ exists z, FirstMember z E⁻¹ W).
      { intro; destruct H9; unfold FirstMember in H9; destruct H9.
        AssE x0; apply Theorem134 in H9; AssE (PlusOne x0).
        apply H10 in H9; elim H9; clear H9 H10.
        unfold Rrelation, Inverse, E; apply AxiomII_P.
        split; try apply Theorem49; auto; apply AxiomII_P.
        split; try apply Theorem49; auto; unfold PlusOne.
        apply Theorem4; right; apply AxiomII; auto. }
      double H5; unfold Section in H10; destruct H10; clear H11.
      apply Lemma97 with (r:= r⁻¹) in H10; auto; clear H6; double H4.
      apply Theorem96 in H6; destruct H6; clear H11; destruct H6 as [H11 H6].
      clear H11; elim H9; clear H9; unfold WellOrdered in H10; destruct H10.
      assert (ran(f⁻¹|W) ⊂ dom(f) /\ ran(f⁻¹|W) ≠ Φ).
      { split; unfold Included; intros.
        - unfold Range in H11; apply AxiomII in H11; destruct H11, H12.
          unfold Restriction in H12; apply Theorem4' in H12; destruct H12.
          unfold Inverse in H12; apply AxiomII_P in H12; destruct H12.
          apply Property_dom in H14; auto.
        - assert (Φ ∈ W); try apply Theorem135; auto; double H11; apply H8 in H12.
          rewrite Lemma96' in H12; apply Property_Value in H12; auto.
          AssE [Φ,(f⁻¹)[Φ]]; apply Theorem49 in H13; destruct H13; apply Lemma35.
          exists f⁻¹[Φ]; unfold Range; apply AxiomII; split; auto.
          exists Φ; unfold Restriction; apply Theorem4'; split; auto.
          apply AxiomII_P; repeat split; try apply Theorem49; auto.
          apply Theorem19; auto. }
      apply H10 in H11; clear H10; destruct H11; exists f[x0].
      unfold FirstMember in H10; destruct H10; unfold FirstMember; split; intros.
      * clear H11; unfold Range in H10; apply AxiomII in H10; destruct H10, H11.
        unfold Restriction in H11; apply Theorem4' in H11; destruct H11.
        apply AxiomII_P in H12; destruct H12; clear H12; destruct H13; clear H13.
        unfold Inverse in H11; apply AxiomII_P in H11; destruct H11; double H13.
        apply Property_dom in H14; apply Property_Value in H14; auto.
        add ([x0,f[x0]] ∈ f) H13; clear H14; unfold Function in H; apply H in H13.
        rewrite H13 in H12; auto.
      * double H12; apply H8 in H13; apply AxiomII in H13; destruct H13, H14.
        AssE [x1,y]; apply Theorem49 in H15; destruct H15; clear H16.
        assert (x1 ∈ ran(f⁻¹|W)).
        { unfold Range; apply AxiomII; split; auto; exists y.
          unfold Restriction; apply Theorem4'; split.
          - unfold Inverse; apply AxiomII_P; split; try apply Theorem49; auto.
          - unfold Cartesian; apply AxiomII_P; repeat split; try apply Theorem49; auto.
            apply Theorem19; auto. }
        apply H11 in H16; clear H11; unfold Range in H10; apply AxiomII in H10.
        destruct H10, H11; unfold Restriction in H11; apply Theorem4' in H11.
        destruct H11; clear H17; unfold Inverse in H11; apply AxiomII_P in H11.
        clear H10; destruct H11; apply Property_dom in H11; double H14.
        apply Property_dom in H17; add (x1 ∈ dom(f)) H11; double H11; clear H17.
        unfold Connect in H9; apply H9 in H18; clear H9; intro.
        unfold Rrelation, Inverse, E in H9; apply AxiomII_P in H9; destruct H9.
        clear H9; apply AxiomII_P in H17; destruct H17.
        destruct H18 as [H18|[H18|H18]]; try contradiction.
        { clear H16; unfold Order_Pr in H4; destruct H11.
          assert (x1 ∈ dom(f) /\ x0 ∈ dom(f) /\ Rrelation x1 r x0).
          { repeat split; auto; unfold Rrelation, Inverse in H18.
            apply AxiomII_P in H18; unfold Rrelation; apply H18. }
          apply H4 in H19; clear H4 H9 H13 H15; unfold Rrelation, E in H19.
          apply AxiomII_P in H19; destruct H19; clear H4.
          apply Property_Value in H16; auto; add ([x1,f[x1]] ∈ f) H14.
          apply H in H14; rewrite H14 in H17; add (f[x1] ∈ f[x0]) H17.
          generalize (Theorem102 f[x0] f[x1]); intros; contradiction. }
        { rewrite H18 in H17; clear H9 H15 H16; destruct H11.
          apply Property_Value in H11; auto; add ([x1,y] ∈ f) H11.
          unfold Function in H; apply H in H11; rewrite H11 in H17.
          generalize (Theorem101 y); intros; contradiction. }
Qed.

Hint Resolve Theorem167 : set.


(* Some properties about finite *)

Lemma Finite_Included : forall (A B: Class),
  Finite A -> B ⊂ A -> Finite B.
Proof.
  intros.
  apply Theorem167 in H; destruct H as [r H], H.
  apply Theorem167; exists r; split.
  - unfold WellOrdered, Connect in H; destruct H.
    unfold WellOrdered, Connect; split; intros.
    + destruct H3; apply H; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
  - unfold WellOrdered, Connect in H1; destruct H1.
    unfold WellOrdered, Connect; split; intros.
    + destruct H3; apply H1; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
Qed.


Lemma Finite_Single : forall z, Ensemble z -> Finite ([z]).
Proof.
  intros.
  apply Theorem167; exists E; split.
  - unfold WellOrdered; split; intros.
    + unfold Connect; intros; destruct H0; unfold Singleton in H0, H1.
      apply AxiomII in H0; apply AxiomII in H1; destruct H0, H1; double H.
      apply Theorem19 in H; apply Theorem19 in H4; apply H2 in H.
      apply H3 in H4; rewrite <- H4 in H; tauto.
    + destruct H0; apply Lemma35 in H1; destruct H1; exists x.
      unfold FirstMember; split; auto; intros; unfold Included in H0.
      apply H0 in H1; apply H0 in H2; unfold Singleton in H1, H2; double H.
      apply AxiomII in H1; apply AxiomII in H2; destruct H1, H2.
      apply Theorem19 in H; apply Theorem19 in H3; apply H4 in H.
      apply H5 in H3; rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation in H6; unfold E in H6; apply AxiomII_P in H6.
      destruct H6; generalize (Theorem101 y0); intros; contradiction.
  - unfold WellOrdered; split; intros.
    + unfold Connect; intros; destruct H0; unfold Singleton in H0, H1.
      apply AxiomII in H0; apply AxiomII in H1; destruct H0, H1; double H.
      apply Theorem19 in H; apply Theorem19 in H4.
      apply H2 in H; apply H3 in H4; rewrite <- H4 in H; tauto.
    + destruct H0; apply Lemma35 in H1; auto; destruct H1; exists x.
      unfold FirstMember; split; auto; intros; unfold Included in H0.
      apply H0 in H1; apply H0 in H2; unfold Singleton in H1, H2; double H.
      apply AxiomII in H1; apply AxiomII in H2; destruct H1, H2.
      apply Theorem19 in H; apply Theorem19 in H3; apply H4 in H.
      apply H5 in H3; rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation in H6; unfold Inverse in H6.
      apply AxiomII_P in H6; destruct H6; unfold E in H7; apply AxiomII_P in H7.
      destruct H7; generalize (Theorem101 y0); intros; contradiction.
Qed.


(* 定理168 如果x与y均有限，则x∪y也有限 *)

Theorem Theorem168 : forall x y,
  Finite x /\ Finite y -> Finite (x ∪ y).
Proof.
  intros; destruct H.
  apply Theorem167 in H; apply Theorem167 in H0.
  destruct H as [r H], H0 as [s H0], H, H0; apply Theorem167.
  exists (\{\ λ u v, (u∈x /\ v∈x /\ Rrelation u r v) \/
  (u∈(y~x) /\ v∈(y~x) /\ Rrelation u s v) \/ (u∈x /\ v∈(y~x)) \}\); split.
  - clear H1 H2; unfold WellOrdered in H, H0; destruct H, H0.
    unfold WellOrdered; split; intros.
    + clear H1 H2; unfold Connect in H, H0; unfold Connect; intros.
      destruct H1; apply Theorem4 in H1; apply Theorem4 in H2.
      unfold Rrelation; destruct H1, H2.
      * clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
        clear H; destruct H0 as [H | [H | H]]; try tauto.
        { left; SplitEnsP. } { right; left; SplitEnsP. }
      * clear H0; generalize (classic (v ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { left; SplitEnsP; right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * clear H0; generalize (classic (u ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { right; left; SplitEnsP.
          right; right; split; auto; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * generalize (classic (u∈x)) (classic (v∈x)); intros; destruct H3, H4.
        { clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
          clear H; destruct H0 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { left; SplitEnsP; right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { right; left; SplitEnsP; right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { clear H; assert (u ∈ y /\ v ∈ y); auto; apply H0 in H.
          clear H0; destruct H as [H | [H | H]]; try tauto.
          - left; SplitEnsP; right; left; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns.
          - right; left; SplitEnsP.
            right; left; unfold Setminus; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns. }
    + generalize (classic (\{ λ z, z ∈ y0 /\ z ∈ x \} = Φ)).
      clear H H0; destruct H3; intros; destruct H3.
      * assert (y0 ⊂ y).
        { unfold Included; intros; double H4.
          apply H in H5; apply Theorem4 in H5; destruct H5; auto.
          generalize (Theorem16 z); intros; elim H6; clear H6.
          rewrite <- H3; apply AxiomII; repeat split; Ens. }
        add (y0 ≠ Φ) H4; apply H2 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply AxiomII_P in H1; destruct H1.
        unfold Rrelation; destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (Theorem16 y1); intros.
          elim H5; rewrite <- H3; apply AxiomII; repeat split; Ens. }
        { destruct H4; clear H5; generalize (Theorem16 y1); intros.
          elim H5; rewrite <- H3; apply AxiomII; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈x\} ⊂ x).
        { unfold Included; intros; apply AxiomII in H4; apply H4. }
        add (\{λ z, z∈y0 /\ z∈x\} <> Φ) H4; apply H1 in H4; clear H1 H2.
        destruct H4 as [z H1]; exists z; unfold FirstMember in H1.
        destruct H1; apply AxiomII in H1; destruct H1, H4.
        unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H7.
        { assert (y1 ∈ \{λ z, z∈y0 /\ z∈x\}).
          { apply AxiomII; repeat split; Ens. }
          apply H2 in H8; intro; elim H8; clear H2 H8.
          unfold Rrelation in H9; apply AxiomII_P in H9; destruct H9.
          unfold Rrelation; destruct H8 as [H8|[H8|H8]]; try apply H8.
          - destruct H8; clear H9; unfold Setminus in H8; apply AxiomII in H8.
            destruct H8, H9; unfold Complement in H10; apply AxiomII in H10.
            destruct H10; contradiction.
          - destruct H8; clear H8; unfold Setminus in H9; apply AxiomII in H9.
            destruct H9, H9; unfold Complement in H10; apply AxiomII in H10.
            destruct H10; contradiction. }
        { intro; unfold Rrelation in H8; apply AxiomII_P in H8.
          destruct H8, H9 as [H9|[H9|H9]], H9; try contradiction.
          destruct H10; clear H8 H9 H11; unfold Setminus in H10.
          apply AxiomII in H10; destruct H10, H9; unfold Complement in H10.
          apply AxiomII in H10; destruct H10; contradiction. }
  - unfold WellOrdered; split; intros.
    + clear H1 H2; unfold WellOrdered in H, H0; destruct H, H0.
      clear H1 H2; unfold Connect in H, H0; unfold Connect; intros.
      destruct H1; apply Theorem4 in H1; apply Theorem4 in H2.
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
          right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * clear H0; generalize (classic (u ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { left; SplitEnsP; SplitEnsP.
          right; right; split; auto; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * generalize (classic (u∈x)) (classic (v∈x)); intros; destruct H3, H4.
        { clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
          clear H; destruct H0 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { right; left; SplitEnsP; SplitEnsP.
          right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { left; SplitEnsP; SplitEnsP.
          right; right; split; auto; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { clear H; assert (u ∈ y /\ v ∈ y); auto; apply H0 in H.
          clear H0; destruct H as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
            right; left; unfold Setminus; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns.
          - left; SplitEnsP; SplitEnsP; right; left; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns. }
    + clear H H0; unfold WellOrdered in H1, H2.
      destruct H1, H2; clear H H1; destruct H3.
      generalize (classic (\{λ z, z∈y0 /\ z∈(y~x)\}=Φ)); intros; destruct H3.
      * assert (y0 ⊂ x).
        { unfold Included; intros; double H4.
          apply H in H5; apply Theorem4 in H5; destruct H5; auto.
          generalize (classic (z ∈ x)); intros; destruct H6; auto.
          generalize (Theorem16 z); intros; elim H7; clear H7.
          rewrite <- H3; apply AxiomII; repeat split; Ens.
          unfold Setminus; apply Theorem4'; split; auto.
          unfold Complement; apply AxiomII; split; Ens. }
        add (y0 ≠ Φ) H4; apply H0 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply AxiomII_P in H1; destruct H1.
        apply AxiomII_P in H4; destruct H4 as [H5 H4]; clear H5.
        unfold Rrelation, Inverse; apply AxiomII_P; split; auto.
        destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (Theorem16 z); intros.
          elim H5; rewrite <- H3; apply AxiomII; repeat split; Ens. }
        { destruct H4; clear H4; generalize (Theorem16 y1); intros.
          elim H4; rewrite <- H3; apply AxiomII; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈(y~x)\} ⊂ y).
        { unfold Included; intros; apply AxiomII in H4; destruct H4, H5.
          unfold Setminus in H6; apply Theorem4' in H6; apply H6. }
        add (\{λ z, z∈y0 /\ z∈(y~x)\} <> Φ) H4; apply H2 in H4; clear H0 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; apply AxiomII in H0; destruct H0, H4.
        unfold Setminus in H5; apply Theorem4' in H5; destruct H5.
        unfold Complement in H6; apply AxiomII in H6; clear H0; destruct H6.
        unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H8.
        { intro; unfold Rrelation in H9; apply AxiomII_P in H9; destruct H9.
          apply AxiomII_P in H10; destruct H10 as [H11 H10]; clear H11.
          destruct H10 as [H10|[H10|H10]], H10; try contradiction.
          destruct H11; clear H9 H10 H12; unfold Setminus in H11.
          apply AxiomII in H11; destruct H11, H10; unfold Complement in H11.
          apply AxiomII in H11; destruct H11; contradiction. }
        { assert (y1 ∈ \{λ z, z ∈ y0 /\ z ∈ (y ~ x)\}).
          { apply AxiomII; repeat split; Ens; apply H in H7.
            apply Theorem4 in H7; destruct H7; try contradiction.
            apply Theorem4'; split; auto; apply AxiomII; split; Ens. }
          apply H2 in H9; intro; elim H9; clear H2 H9.
          unfold Rrelation in H10; apply AxiomII_P in H10; destruct H10.
          apply AxiomII_P in H9; destruct H9 as [H10 H9]; clear H10.
          unfold Rrelation, Inverse; SplitEnsP.
          destruct H9 as [H9|[H9|H9]], H9; try contradiction; apply H10. }
Qed.

Hint Resolve Theorem168 : set.


(* 定理169 如果x有限且x的每个元有限，则∪x也有限 *)

Lemma Lemma169 : forall x y, x ∈ y -> y = (y ~ [x] ∪ [x]).
Proof.
  intros.
  apply AxiomI; split; intros.
  - generalize (classic (z ∈ [x])); intros; destruct H1.
    + apply Theorem4; right; auto.
    + apply Theorem4; left; unfold Setminus; apply Theorem4'.
      split; auto; unfold Complement; apply AxiomII; Ens.
  - apply Theorem4 in H0; destruct H0.
    + unfold Setminus in H0; apply Theorem4' in H0; apply H0.
    + unfold Singleton in H0; apply AxiomII in H0; destruct H0.
      rewrite H1; try apply Theorem19; Ens.
Qed.

Lemma Lemma169' : forall x y, ∪(x ∪ y) = (∪x) ∪ (∪y).
Proof.
  intros.
  apply AxiomI; split; intros.
  - apply AxiomII in H; destruct H, H0, H0.
    apply Theorem4 in H1; destruct H1.
    + apply Theorem4; left; apply AxiomII; Ens.
    + apply Theorem4; right; apply AxiomII; Ens.
  - apply Theorem4 in H; destruct H.
    + apply AxiomII in H; destruct H, H0, H0.
      apply AxiomII; split; Ens; exists x0.
      split; auto; apply Theorem4; auto.
    + apply AxiomII in H; destruct H, H0, H0.
      apply AxiomII; split; auto; exists x0.
      split; auto; apply Theorem4; auto.
Qed.

Theorem Theorem169 : forall (x: Class),
  Finite x -> (forall z, z∈x -> Finite z) -> Finite (∪ x).
Proof.
  intros; double H.
  unfold Finite in H; apply Property_Finite in H1.
  assert (\{λ u, u∈W /\ (forall y, P[y] = u /\ Ensemble y /\
            (forall z, z∈y -> Finite z) -> Finite (∪ y)) \} = W).
  { apply Theorem137.
    - unfold Included; intros; apply AxiomII in H2; apply H2.
    - apply AxiomII; generalize (Theorem135 x); intros; destruct H2.
      clear H3; repeat split; Ens; intros; destruct H3, H4.
      generalize (classic (y = Φ)); intros; destruct H6.
      + rewrite H6 in *; rewrite Theorem24'; unfold Finite; rewrite H3; auto.
      + apply Lemma35 in H6; destruct H6; apply Theorem153 in H1.
        apply Theorem153 in H4; apply Theorem146 in H4; unfold Equivalent in H4.
        destruct H4 as [f H4], H4, H4, H7; rewrite <- H7 in H6.
        apply Property_Value in H6; auto; apply Property_ran in H6.
        rewrite H9, H3 in H6; generalize (Theorem16 f[x0]); contradiction.
    - intros; apply AxiomII in H2; apply AxiomII; destruct H2, H3; double H3.
      apply Theorem134 in H5; repeat split; Ens; intros; destruct H6, H7.
      AssE y; clear H7; double H9; unfold PlusOne in H6; apply Theorem153 in H9.
      unfold Equivalent in H9; destruct H9 as [f H9], H9, H9, H10.
      assert (u ∈ P[y]).
      { rewrite H6; apply Theorem4; right; unfold Singleton.
        apply AxiomII; split; Ens. }
      rewrite <- H10 in H13; apply Property_Value in H13; auto.
      apply Property_ran in H13; rewrite H12 in H13.
      apply Lemma169 in H13; rewrite H13; clear H13.
      rewrite Lemma169'; apply Theorem168; split.
      + apply H4; assert (Ensemble (y ~ [f[u]])).
        { apply (Theorem33 y _); auto; unfold Included; intros.
          unfold Setminus in H13; apply Theorem4' in H13; apply H13. }
        repeat split; auto; intros.
        * apply Theorem164 in H3; apply Theorem156 in H3; clear H2; destruct H3.
          rewrite <- H3 at 2; add (Ensemble u) H13; apply Theorem154 in H13.
          apply H13; clear H13; apply Theorem146; unfold Equivalent.
          exists (f|(P[y]~[u])).
          { repeat split; unfold Relation; intros.
            - unfold Restriction in H13; apply Theorem4' in H13.
              destruct H13; PP H14 a b; Ens.
            - unfold Restriction in H13; destruct H13; apply Theorem4' in H13.
              apply Theorem4' in H14; destruct H13, H14; unfold Function in H9.
              apply H9 with (x:= x0); split; auto.
            - PP H13 a b; Ens.
            - unfold Inverse, Restriction in H13; destruct H13.
              apply AxiomII_P in H13; apply AxiomII_P in H14; destruct H13, H14.
              apply Theorem4' in H15; apply Theorem4' in H16; destruct H15, H16.
              clear H17 H18; unfold Function in H11; apply H11 with (x:= x0).
              split; apply AxiomII_P; Ens.
            - apply AxiomI; split; intros.
              + unfold Domain in H13; apply AxiomII in H13; destruct H13, H14.
                unfold Restriction in H14; apply Theorem4' in H14; destruct H14.
                clear H14; unfold Cartesian in H15; apply AxiomII_P in H15.
                destruct H15, H15; clear H16; unfold Setminus in H15.
                apply Theorem4' in H15; destruct H15; rewrite H6 in H15.
                apply Theorem4 in H15; destruct H15; auto.
                unfold Complement in H16; apply AxiomII in H16; destruct H16.
                contradiction.
              + unfold Domain; apply AxiomII; split; Ens; exists f[z].
                unfold Restriction; apply Theorem4'.
                assert (z ∈ dom(f)). { rewrite H10, H6; apply Theorem4; tauto. }
                apply Property_Value in H14; auto; split; auto.
                unfold Cartesian; apply AxiomII_P; split; Ens; double H14.
                apply Property_ran in H15; split; try apply Theorem19; Ens.
                clear H15; apply Property_dom in H14; unfold Setminus.
                apply Theorem4'; rewrite H10 in H14; split; auto.
                unfold Complement; apply AxiomII; split; Ens; intro.
                apply AxiomII in H15; destruct H15.
                rewrite H16 in H13; try apply Theorem19; Ens.
                generalize (Theorem101 u); intros; contradiction.
            - apply AxiomI; split; intros.
              + unfold Range in H13; apply AxiomII in H13; destruct H13, H14.
                unfold Restriction in H14; apply Theorem4' in H14; destruct H14.
                unfold Cartesian in H15; apply AxiomII_P in H15; destruct H15.
                clear H15; destruct H16; clear H16; unfold Setminus in H15.
                apply Theorem4' in H15; destruct H15; double H15.
                rewrite <- H10 in H15; rewrite H6 in H17.
                apply Theorem4 in H17; destruct H17.
                * clear H17; apply Property_Value in H15; auto.
                  add ([x0,z] ∈ f) H15; apply H9 in H15; rewrite <- H15 in *.
                  clear H15; unfold Setminus; apply Theorem4'; double H14.
                  apply Property_ran in H15; rewrite H12 in H15; split; auto.
                  unfold Complement; apply AxiomII; split; Ens; intro.
                  apply AxiomII in H17; destruct H17; assert (u ∈ dom(f)).
                  { rewrite H10, H6; apply Theorem4; right.
                    unfold Singleton; apply AxiomII; Ens. }
                  apply Property_Value in H19; auto; AssE [u,f[u]].
                  apply Theorem49 in H20; destruct H20.
                  rewrite H18 in H14; try apply Theorem19; Ens.
                  unfold Complement in H16; apply AxiomII in H16; destruct H16.
                  elim H22; unfold Singleton; apply AxiomII; split; Ens; intros.
                  apply H11 with (x:= f[u]); unfold Inverse.
                  split; apply AxiomII_P; split; try apply Theorem49; auto.
                * unfold Complement in H16; apply AxiomII in H16.
                  destruct H16; contradiction.
              + unfold Setminus in H13; apply Theorem4' in H13; destruct H13.
                rewrite <- H12 in H13; apply AxiomII in H13; destruct H13, H15.
                unfold Range; apply AxiomII; split; Ens; exists x0.
                unfold Restriction; apply Theorem4'; split; auto.
                unfold Cartesian; apply AxiomII_P; split; Ens.
                split; try apply Theorem19; Ens; apply Theorem4'; double H15.
                apply Property_dom in H16; rewrite <- H10; split; auto.
                unfold Complement; apply AxiomII; split; Ens; intro.
                apply AxiomII in H17; destruct H17.
                rewrite H18 in *; try apply Theorem19; Ens.
                apply Property_Value in H16; auto; clear H17 H18.
                add ([u,z] ∈ f) H16; apply H9 in H16; rewrite H16 in H14.
                unfold Complement in H14; apply AxiomII in H14; clear H13.
                destruct H14; elim H14; apply AxiomII; Ens. }
        * unfold Setminus in H14; apply Theorem4' in H14; destruct H14.
          apply H8; auto.
      + assert (f[u] ∈ y).
        { assert (u ∈ dom(f)).
          { rewrite H10, H6; apply Theorem4; right; apply AxiomII; Ens. }
          apply Property_Value in H13; auto; apply Property_ran in H13.
          rewrite H12 in H13; auto. }
        AssE f[u]; apply Theorem44 in H14; destruct H14; rewrite H15.
        clear H14 H15; apply H8; auto. }
  rewrite <- H2 in H; clear H2; apply AxiomII in H; destruct H, H2.
  apply H3; repeat split; auto.
Qed.

Hint Resolve Theorem169 : set.


(* 定理170 如果x与y有限，则x×y也有限 *)

Theorem Theorem170 : forall x y,
  Finite x /\ Finite y -> Finite (x × y).
Proof.
  intros; destruct H.
  generalize (classic (y = Φ)); intros; destruct H1.
  - rewrite H1 in *; clear H1.
    assert ((x × Φ) = Φ).
    { apply AxiomI; split; intros.
      - PP H1 a b; apply AxiomII_P in H2; destruct H2, H3.
        generalize (Theorem16 b); intros; contradiction.
      - generalize (Theorem16 z); intros; contradiction. }
    rewrite H1; auto.
  - assert (∪ \{ λ u, exists v, v∈x /\ u = ([v] × y) \} = x × y).
    { clear H1; apply AxiomI; split; intros.
      - unfold Element_U in H1; apply AxiomII in H1; destruct H1, H2, H2.
        apply AxiomII in H3; destruct H3, H4, H4; unfold Cartesian.
        rewrite H5 in H2; PP H2 a b; apply AxiomII_P in H6; destruct H6, H7.
        apply AxiomII_P; repeat split; auto; unfold Singleton in H7.
        apply AxiomII in H7; destruct H7; rewrite H9; try apply Theorem19; Ens.
      - unfold Cartesian in H1; PP H1 a b; apply AxiomII_P in H2.
        destruct H2, H3; apply AxiomII; split; auto; exists ([a] × y); split.
        + unfold Cartesian; apply AxiomII_P; repeat split; auto.
          unfold Singleton; apply AxiomII; split; Ens.
        + apply AxiomII; split; Ens; apply Theorem73; split; Ens.
          apply Property_Finite; auto. }
    rewrite <- H2; clear H2; apply Theorem169; intros.
    + assert (x ≈ \{ λ u, exists v, v∈x /\ u = ([v] × y) \}).
      { unfold Equivalent; exists (\{\ λ u v, u∈x /\ v = ([u] × y) \}\).
        repeat split; intros; try (unfold Relation; intros; PP H2 a b; Ens).
        - destruct H2; apply AxiomII_P in H2; apply AxiomII_P in H3.
          destruct H2, H3, H4, H5; rewrite H6, H7; auto.
        - destruct H2; apply AxiomII_P in H2; apply AxiomII_P in H3.
          destruct H2, H3; clear H2 H3; apply AxiomII_P in H4.
          apply AxiomII_P in H5; destruct H4, H5, H3, H5; rewrite H7 in H6.
          clear H7; generalize (classic (y0 = z)); intros; destruct H7; auto.
          elim H7; clear H7; apply Lemma35 in H1; destruct H1.
          assert ([y0,x1] ∈ ([z] × y)).
          { rewrite H6; unfold Cartesian; apply AxiomII_P.
            repeat split; try apply Theorem49; Ens.
            unfold Singleton; apply AxiomII; split; Ens. }
          unfold Cartesian in H7; apply AxiomII_P in H7; destruct H7, H8.
          unfold Singleton in H8; apply AxiomII in H8; destruct H8.
          apply H10; apply Theorem19; Ens.
        - apply AxiomI; split; intros.
          + unfold Domain in H2; apply AxiomII in H2; destruct H2, H3.
            apply AxiomII_P in H3; apply H3.
          + unfold Domain; apply AxiomII; split; Ens.
            exists ([z] × y); apply AxiomII_P; repeat split; auto.
            apply Theorem49; split; Ens; apply Property_Finite in H0.
            apply Theorem73; split; Ens.
        - apply AxiomI; split; intros.
          + unfold Range in H2; apply AxiomII in H2; destruct H2, H3.
            apply AxiomII_P in H3; destruct H3, H4; apply AxiomII; split; Ens.
          + apply AxiomII in H2; destruct H2, H3, H3.
            unfold Range; apply AxiomII; split; auto; exists x0.
            apply AxiomII_P; repeat split; try apply Theorem49; Ens. }
      assert (Ensemble x /\ Ensemble \{λ u, exists v, v∈x/\u=([v]×y)\}).
      { apply Property_Finite in H; apply Property_Finite in H0; split; auto.
        assert (Ensemble pow(x × y)).
        { apply Theorem38; auto; apply Theorem74; split; auto. }
        apply (Theorem33 pow(x × y) _); auto; unfold Included; intros.
        apply AxiomII in H4; destruct H4, H5, H5; rewrite H6 in *; clear H6.
        unfold PowerSet; apply AxiomII; split; auto; unfold Included; intros.
        PP H6 a b; apply AxiomII_P in H7; destruct H7, H8; apply AxiomII_P.
        repeat split; auto; unfold Singleton in H8; apply AxiomII in H8.
        destruct H8; rewrite H10; try apply Theorem19; Ens. }
      apply Theorem154 in H3; apply H3 in H2; clear H3.
      unfold Finite; unfold Finite in H; rewrite <- H2; auto.
    + apply AxiomII in H2; destruct H2, H3, H3; rewrite H4 in *; clear H4.
      assert (y ≈ ([x0] × y)).
      { unfold Equivalent; exists (\{\ λ u v, u∈y /\ v = [x0,u] \}\).
        repeat split; intros; try (unfold Relation; intros; PP H4 a b; Ens).
        - destruct H4; apply AxiomII_P in H4; apply AxiomII_P in H5.
          destruct H4, H5, H6, H7; rewrite H8, H9; auto.
        - destruct H4; apply AxiomII_P in H4; apply AxiomII_P in H5.
          destruct H4, H5; clear H4 H5; apply AxiomII_P in H6.
          apply AxiomII_P in H7; destruct H6, H7, H5, H7; rewrite H9 in H8.
          apply Theorem55 in H8; destruct H8; Ens.
        - apply AxiomI; split; intros.
          + unfold Domain in H4; apply AxiomII in H4; destruct H4, H5.
            apply AxiomII_P in H5; apply H5.
          + unfold Domain; apply AxiomII; split; Ens.
            exists [x0,z0]; apply AxiomII_P; repeat split; auto.
            apply Theorem49; split; Ens; apply Theorem49; Ens.
        - apply AxiomI; split; intros.
          + unfold Range in H4; apply AxiomII in H4; destruct H4, H5.
            apply AxiomII_P in H5; destruct H5, H6; rewrite H7 in *; clear H7.
            apply AxiomII_P; repeat split; auto; unfold Singleton.
            apply AxiomII; split; Ens.
          + PP H4 a b; apply AxiomII_P in H5; destruct H5, H6.
            unfold Range; apply AxiomII; split; auto; exists b.
            apply AxiomII_P; repeat split; try apply Theorem49; Ens.
            unfold Singleton in H6; apply AxiomII in H6; destruct H6.
            rewrite H8; try apply Theorem19; Ens. }
      assert (Ensemble y /\ Ensemble ([x0] × y)).
      { apply Property_Finite in H; apply Property_Finite in H0; Ens. }
      apply Theorem154 in H5; apply H5 in H4; clear H5.
      unfold Finite; unfold Finite in H0; rewrite <- H4; auto.
Qed.

Hint Resolve Theorem170 : set.


(* 定理171 如果x是有限的，则pow(x)也是有限的 *)

Lemma Lemma171 : forall x y,
  y∈x -> pow(x) = pow(x~[y]) ∪ (\{λ z, z ⊂ x /\ y ∈ z\}).
Proof.
  intros; unfold PowerSet; apply AxiomI.
  split; intros; apply AxiomII in H0; destruct H0; apply AxiomII; split; auto.
  - generalize (classic (y ∈ z)); intros; destruct H2.
    + right; apply AxiomII; split; auto.
    + left; apply AxiomII; split; auto; unfold Included; intros; double H3.
      unfold Setminus; apply Theorem4'; apply H1 in H4; split; auto.
      unfold Complement; apply AxiomII; split; Ens; intro.
      unfold Singleton in H5; apply AxiomII in H5; destruct H5.
      rewrite H6 in H3; try contradiction; apply Theorem19; Ens.
  - destruct H1; apply AxiomII in H1; try apply H1; clear H0; destruct H1.
    unfold Included; intros; apply H1 in H2; unfold Setminus in H2.
    apply Theorem4' in H2; apply H2.
Qed.

Theorem Theorem171 : forall (x: Class),
  Finite x -> Finite pow(x).
Proof.
  intros; double H.
  unfold Finite in H; apply Property_Finite in H0.
  assert (\{λ u, u∈W /\ (forall y, P[y] = u /\ Ensemble y -> Finite pow(y))\}
            = W).
  { apply Theorem137.
    - unfold Included; intros; apply AxiomII in H1; apply H1.
    - apply AxiomII; generalize (Theorem135 x); intros; destruct H1.
      clear H2; repeat split; Ens; intros; destruct H2; AssE y; clear H3.
      generalize (classic (y = Φ)); intros; destruct H3.
      + assert (pow(Φ) = [Φ]).
        { unfold PowerSet, Singleton; apply AxiomI.
          split; intros; apply AxiomII in H5; destruct H5; apply AxiomII.
          - split; auto; intros; add (Φ ⊂ z) H6; try apply Theorem26.
            apply Theorem27 in H6; auto.
          - split; auto; rewrite H6; try apply Theorem19; Ens.
            unfold Included; intros; auto. }
        rewrite H3 in *; rewrite H5; apply Finite_Single; Ens.
      + apply Lemma35 in H3; destruct H3; apply Theorem153 in H4.
        apply Theorem146 in H4; unfold Equivalent in H4.
        destruct H4 as [f H4], H4, H4, H5; rewrite <- H5 in H3.
        apply Property_Value in H3; auto; apply Property_ran in H3.
        rewrite H7, H2 in H3; generalize (Theorem16 f[x0]); contradiction.
    - intros; apply AxiomII in H1; apply AxiomII; destruct H1, H2; double H2.
      apply Theorem134 in H4; repeat split; Ens; intros; destruct H5.
      AssE y; clear H6; double H7; unfold PlusOne in H5; apply Theorem153 in H7.
      unfold Equivalent in H7; destruct H7 as [f H7], H7, H7, H8.
      assert (u ∈ P[y]).
      { rewrite H5; apply Theorem4; right; unfold Singleton.
        apply AxiomII; split; Ens. }
      double H11; rewrite <- H8 in H12; apply Property_Value in H12; auto.
      apply Property_ran in H12; rewrite H10 in H12; apply Lemma171 in H12.
      rewrite H12; clear H12; apply Theorem168.
      assert (Finite pow(y ~ [f[u]])).
      { apply H3; assert (Ensemble (y ~ [f[u]])).
        { apply (Theorem33 y _); auto; unfold Included; intros.
          unfold Setminus in H12; apply Theorem4' in H12; apply H12. }
        repeat split; auto; intros; apply Theorem164 in H2.
        apply Theorem156 in H2; clear H1; destruct H2.
        rewrite <- H2 at 2; add (Ensemble u) H12; apply Theorem154 in H12.
        apply H12; clear H12; apply Theorem146; unfold Equivalent.
        exists (f|(P[y]~[u])).
        { repeat split; unfold Relation; intros.
          - unfold Restriction in H12; apply Theorem4' in H12.
            destruct H12; PP H13 a b; Ens.
          - unfold Restriction in H12; destruct H12; apply Theorem4' in H12.
            apply Theorem4' in H13; destruct H12, H13; unfold Function in H7.
            apply H7 with (x:= x0); split; auto.
          - PP H12 a b; Ens.
          - unfold Inverse, Restriction in H12; destruct H12.
            apply AxiomII_P in H12; apply AxiomII_P in H13; destruct H12, H13.
            apply Theorem4' in H14; apply Theorem4' in H15; destruct H14, H15.
            clear H16 H17; unfold Function in H9; apply H9 with (x:= x0).
            split; apply AxiomII_P; Ens.
          - apply AxiomI; split; intros.
            + unfold Domain in H12; apply AxiomII in H12; destruct H12, H13.
              unfold Restriction in H13; apply Theorem4' in H13; destruct H13.
              clear H13; unfold Cartesian in H14; apply AxiomII_P in H14.
              destruct H14, H14; clear H15; unfold Setminus in H14.
              apply Theorem4' in H14; destruct H14; rewrite H5 in H14.
              apply Theorem4 in H14; destruct H14; auto.
              apply AxiomII in H15; destruct H15; contradiction.
            + unfold Domain; apply AxiomII; split; Ens; exists f[z].
              unfold Restriction; apply Theorem4'.
              assert (z ∈ dom(f)). { rewrite H8, H5; apply Theorem4; tauto. }
              apply Property_Value in H13; auto; split; auto.
              unfold Cartesian; apply AxiomII_P; split; Ens; double H13.
              apply Property_ran in H14; split; try apply Theorem19; Ens.
              clear H14; apply Property_dom in H13; unfold Setminus.
              apply Theorem4'; rewrite H8 in H13; split; auto.
              unfold Complement; apply AxiomII; split; Ens; intro.
              apply AxiomII in H14; destruct H14.
              rewrite H15 in H12; try apply Theorem19; Ens.
              generalize (Theorem101 u); intros; contradiction.
          - apply AxiomI; split; intros.
            + unfold Range in H12; apply AxiomII in H12; destruct H12, H13.
              unfold Restriction in H13; apply Theorem4' in H13; destruct H13.
              unfold Cartesian in H14; apply AxiomII_P in H14; destruct H14.
              clear H14; destruct H15; clear H15; unfold Setminus in H14.
              apply Theorem4' in H14; destruct H14; double H14.
              rewrite <- H8 in H14; rewrite H5 in H16.
              apply Theorem4 in H16; destruct H16.
              * clear H16; apply Property_Value in H14; auto.
                add ([x0,z] ∈ f) H14; apply H7 in H14; rewrite <- H14 in *.
                clear H14; unfold Setminus; apply Theorem4'; double H13.
                apply Property_ran in H14; rewrite H10 in H14; split; auto.
                unfold Complement; apply AxiomII; split; Ens; intro.
                apply AxiomII in H16; destruct H16; assert (u ∈ dom(f)).
                { rewrite H8, H5; apply Theorem4; right.
                  unfold Singleton; apply AxiomII; Ens. }
                apply Property_Value in H18; auto; AssE [u,f[u]].
                apply Theorem49 in H19; destruct H19.
                rewrite H17 in H13; try apply Theorem19; Ens.
                unfold Complement in H15; apply AxiomII in H15; destruct H15.
                elim H21; unfold Singleton; apply AxiomII; split; Ens; intros.
                apply H9 with (x:= f[u]); unfold Inverse.
                split; apply AxiomII_P; split; try apply Theorem49; auto.
              * unfold Complement in H15; apply AxiomII in H15.
                destruct H15; contradiction.
            + unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
              rewrite <- H10 in H12; apply AxiomII in H12; destruct H12, H14.
              unfold Range; apply AxiomII; split; Ens; exists x0.
              unfold Restriction; apply Theorem4'; split; auto.
              unfold Cartesian; apply AxiomII_P; split; Ens.
              split; try apply Theorem19; Ens; apply Theorem4'.
              double H14; apply Property_dom in H15; rewrite <- H8; split; auto.
              unfold Complement; apply AxiomII; split; Ens; intro.
              apply AxiomII in H16; destruct H16.
              rewrite H17 in *; try apply Theorem19; Ens.
              apply Property_Value in H15; auto; clear H16 H17.
              add ([u,z] ∈ f) H15; apply H7 in H15; rewrite H15 in H13.
              unfold Complement in H13; apply AxiomII in H13; clear H12.
              destruct H13; elim H13; apply AxiomII; Ens. } }
      split; auto.
      assert (pow(y ~ [f[u]]) ≈ \{λ z, z ⊂ y /\ f[u] ∈ z\}).
      { unfold Equivalent.
        exists (\{\ λ v w, v ∈ pow(y~[f[u]]) /\ w = v ∪ [f[u]] \}\).
        repeat split; unfold Relation; intros; try PP H13 a b; Ens.
        - destruct H13; apply AxiomII_P in H13; apply AxiomII_P in H14.
          destruct H13, H14, H15, H16; rewrite H17, H18; auto.
        - destruct H13; apply AxiomII_P in H13; apply AxiomII_P in H14.
          destruct H13, H14; clear H13 H14; apply AxiomII_P in H15.
          apply AxiomII_P in H16; destruct H15, H16, H14, H16.
          rewrite H18 in H17; clear H13 H15 H18; unfold PowerSet in H14, H16.
          apply AxiomII in H14; apply AxiomII in H16; destruct H14, H16.
          apply AxiomI; split; intros.
          + assert (z0 ∈ (y0 ∪ [f[u]])). { apply Theorem4; tauto. }
            rewrite <- H17 in H19; apply Theorem4 in H19; destruct H19; auto.
            apply H14 in H18; unfold Setminus in H18; apply Theorem4' in H18.
            destruct H18; unfold Complement in H20; apply AxiomII in H20.
            destruct H20; contradiction.
          + assert (z0 ∈ (z ∪ [f[u]])). { apply Theorem4; tauto. }
            rewrite H17 in H19; apply Theorem4 in H19; destruct H19; auto.
            apply H16 in H18; unfold Setminus in H18; apply Theorem4' in H18.
            destruct H18; unfold Complement in H20; apply AxiomII in H20.
            destruct H20; contradiction.
        - unfold Domain; apply AxiomI; split; intros.
          + apply AxiomII in H13; destruct H13, H14.
            apply AxiomII_P in H14; apply H14.
          + apply AxiomII; split; Ens; exists (z ∪ [f[u]]).
            apply AxiomII_P; repeat split; auto; apply Theorem49.
            split; Ens; apply AxiomIV; split; Ens.
            rewrite <- H8 in H11; apply Property_Value in H11; auto.
            apply Property_ran in H11; AssE f[u]; apply Theorem42; auto.
        - unfold Range; apply AxiomI; split; intros.
          + apply AxiomII in H13; destruct H13, H14; apply AxiomII_P in H14.
            destruct H14, H15; apply AxiomII; split; auto; rewrite H16.
            clear H16; unfold PowerSet in H15; apply AxiomII in H15.
            destruct H15; rewrite <- H8 in H11.
            apply Property_Value in H11; auto; apply Property_ran in H11.
            rewrite H10 in H11; split.
            * unfold Included; intros; apply Theorem4 in H17; destruct H17.
              { apply H16 in H17; apply Theorem4' in H17; apply H17. }
              { apply AxiomII in H17; destruct H17.
                rewrite H18; try apply Theorem19; Ens. }
            * apply Theorem4; right; apply AxiomII; split; Ens.
          + apply AxiomII in H13; destruct H13, H14; apply AxiomII.
            split; auto; exists (z~[f[u]]); apply AxiomII_P.
            assert (Ensemble (z ~ [f[u]])).
            { apply Theorem33 with (x:= z); auto; unfold Included.
              intros; apply AxiomII in H16; apply H16. }
            repeat split.
            * apply Theorem49; split; auto.
            * unfold PowerSet; apply AxiomII; split; auto; unfold Setminus.
              unfold Included; intros; apply AxiomII in H17; destruct H17, H18.
              apply Theorem4'; split; auto.
            * apply AxiomI; split; intros.
              { generalize (classic (z0=f[u])); intros.
                apply Theorem4; destruct H18.
                - right; apply AxiomII; split; Ens.
                - left; unfold Setminus; apply Theorem4'; split; auto.
                  apply AxiomII; split; Ens; intro; apply AxiomII in H19.
                  destruct H19; rewrite H20 in H18; try tauto.
                  apply Theorem19; Ens. }
              { apply Theorem4 in H17; destruct H17.
                - unfold Setminus in H17; apply Theorem4' in H17; apply H17.
                - unfold Singleton; apply AxiomII in H17; destruct H17.
                  rewrite H18; auto; apply Theorem19; Ens. } }
      double H12; apply Property_Finite in H14; unfold Finite in H12.
      unfold Finite; apply Theorem154 in H13; try rewrite <- H13; auto.
      split; auto; clear H13 H15; apply Theorem38 in H6; auto.
      apply Theorem33 with (x:= pow(y)); auto; unfold Included at 1; intros.
      apply AxiomII in H13; destruct H13, H14, H15; unfold PowerSet.
      apply AxiomII; split; auto. }
  rewrite <- H1 in H; clear H1; apply AxiomII in H; destruct H, H1.
  apply H2; split; auto.
Qed.

Hint Resolve Theorem171 : set.


(* 定理172 如果x是有限的，y⊂x且P[y]=P[y]，则x=y *)

Theorem Theorem172 : forall x y,
  Finite x -> y ⊂ x -> P[y] = P[x] -> x = y.
Proof.
  intros.
  double H; apply Property_Finite in H2; symmetry.
  double H; unfold Finite in H3; unfold W in H3; apply AxiomII in H3.
  destruct H3; unfold Integer in H4; destruct H4; unfold WellOrdered in H5.
  double H2; apply Theorem153 in H6; apply Theorem146 in H6.
  unfold Equivalent in H6; destruct H6 as [f H6], H6, H6, H7.
  generalize (classic (y = x)); intros; destruct H10; auto.
  assert (y ⊊ x). { unfold ProperSubset; split; auto. }
  apply Property_ProperSubset' in H11; destruct H11 as [z H11], H11.
  generalize (classic (P[x] = Φ)); intros; destruct H13.
  - rewrite <- H7 in H11; apply Property_Value in H11; auto.
    apply Property_ran in H11; rewrite H9, H13 in H11.
    generalize (Theorem16 f[z]); intros; contradiction.
  - assert (P[x] ⊂ P [x] /\ P[x] ≠ Φ). { split; unfold Included; Ens. }
    apply H5 in H14; clear H5 H13; destruct H14 as [u H5].
    assert (P[x] ∈ R /\ LastMember u E P[x]).
    { split; auto; unfold R; apply AxiomII; split; auto. }
    apply Theorem133 in H13; unfold FirstMember in H5; destruct H5; clear H14.
    assert ((x ~ [z]) ≈ u).
    { rewrite <- H9 in H5; apply AxiomII in H5; destruct H5; clear H5.
      destruct H14; rewrite <- H7 in H11; apply Property_Value in H11; auto.
      generalize (classic (z = x0)); intros; destruct H14.
      - rewrite H14; unfold Equivalent; exists (f | (x ~ [x0])).
        repeat split; unfold Relation; intros.
        + apply Theorem4' in H15; destruct H15; PP H16 a b; Ens.
        + unfold Restriction in H15; destruct H15; apply Theorem4' in H15.
          apply Theorem4' in H16; destruct H15, H16; apply H6 with (x:= x1); auto.
        + PP H15 a b; Ens.
        + unfold Inverse, Restriction in H15; destruct H15.
          apply AxiomII_P in H15; apply AxiomII_P in H16; destruct H15, H16.
          apply Theorem4' in H17; apply Theorem4' in H18; destruct H17, H18.
          apply H8 with (x:= x1); unfold Inverse; split; apply AxiomII_P; Ens.
        + apply AxiomI; split; intros.
          * unfold Domain in H15; apply AxiomII in H15; destruct H15, H16.
            unfold Restriction in H16; apply Theorem4' in H16; destruct H16.
            unfold Cartesian in H17; apply AxiomII_P in H17; apply H17.
          * unfold Domain; apply AxiomII; split; Ens; exists f[z0]; double H15.
            unfold Setminus in H16; apply Theorem4' in H16; destruct H16.
            clear H17; rewrite <- H7 in H16; apply Property_Value in H16; auto.
            unfold Restriction; apply Theorem4'; split; auto; unfold Cartesian.
            apply AxiomII_P; repeat split; Ens; apply Property_ran in H16.
            apply Theorem19; Ens.
        + apply AxiomI; split; intros.
          * unfold Range in H15; apply AxiomII in H15; destruct H15, H16.
            apply Theorem4' in H16; destruct H16; double H16.
            apply Property_ran in H18; rewrite H9, H13 in H18.
            unfold PlusOne in H18; apply Theorem4 in H18; destruct H18; auto.
            apply AxiomII in H18; destruct H18; unfold Cartesian in H17.
            apply AxiomII_P in H17; destruct H17, H20; clear H17 H18 H21.
            unfold Setminus in H20; apply Theorem4' in H20; destruct H20.
            clear H17; unfold Complement in H18; apply AxiomII in H18.
            destruct H18; elim H18; clear H18; unfold Singleton; apply AxiomII.
            split; auto; intros; clear H17 H18; apply H8 with (x:= u).
            AssE [x0,u]; apply Theorem49 in H17; destruct H17.
            rewrite H19 in H16; try apply Theorem19; Ens; clear H19.
            split; apply AxiomII_P; split; try apply Theorem49; auto.
            apply Property_dom in H16; split; Ens.
          * unfold Range; apply AxiomII; split; Ens; assert (z0 ∈ ran(f)).
            { rewrite H9, H13; unfold PlusOne; apply Theorem4; tauto. }
            unfold Range in H16; apply AxiomII in H16; destruct H16, H17.
            exists x1; unfold Restriction; apply Theorem4'; split; auto.
            unfold Cartesian; apply AxiomII_P; split; Ens; double H17.
            split; try apply Theorem19; auto; unfold Setminus.
            apply Property_dom in H18; rewrite H7 in H18; apply Theorem4'.
            split; auto; unfold Complement; apply AxiomII; split; Ens; intro.
            unfold Singleton in H19; apply AxiomII in H19; destruct H19.
            double H5; apply Property_dom in H21; clear H18 H19.
            rewrite H20 in H17; try apply Theorem19; Ens; clear H20 H21.
            add ([x0,z0] ∈ f) H5; apply H6 in H5; clear H17.
            rewrite H5 in H15; generalize (Theorem101 z0); contradiction.
      - unfold Equivalent; exists (\{\ λ v w, v ∈ (x ~ [z]) /\
        (v = x0 -> w = f[z]) /\ (v <> x0 -> [v,w] ∈ f) \}\).
        repeat split; unfold Relation; intros; try PP H15 a b; Ens.
        + destruct H15; apply AxiomII_P in H15; apply AxiomII_P in H16.
          destruct H15, H16, H17, H18; generalize (classic (x1 = x0)); intros.
          destruct H21; double H21; apply H19 in H21; apply H20 in H22.
          * rewrite H21, H22; auto.
          * apply H6 with (x:= x1); auto.
        + destruct H15; apply AxiomII_P in H15; apply AxiomII_P in H16.
          destruct H15, H16; apply AxiomII_P in H17; apply AxiomII_P in H18.
          destruct H17, H18; clear H17 H18; destruct H19, H20.
          apply Theorem4' in H17; apply Theorem4' in H19; destruct H17, H19.
          generalize (classic (y0 = x0)) (classic (z0 = x0)); intros.
          destruct H23, H24; try rewrite H23, H24; apply H18 in H23;
          apply H20 in H24; clear H18 H20; auto.
          * rewrite <- H23 in H11; clear H23.
            assert ([x1,z] ∈ f⁻¹ /\ [x1,z0] ∈ f⁻¹).
            { unfold Inverse; split; apply AxiomII_P; split; Ens.
              AssE [z,x1]; apply Theorem49; apply Theorem49 in H18; tauto. }
            apply H8 in H18; rewrite <- H18 in H22; clear H18 H24.
            apply AxiomII in H22; destruct H22; elim H20; apply AxiomII; Ens.
          * rewrite <- H24 in H11; clear H24.
            assert ([x1,z] ∈ f⁻¹ /\ [x1,y0] ∈ f⁻¹).
            { unfold Inverse; split; apply AxiomII_P; split; Ens.
              AssE [z,x1]; apply Theorem49; apply Theorem49 in H18; tauto. }
            apply H8 in H18; rewrite <- H18 in H21; clear H16 H18 H19 H22 H23.
            apply AxiomII in H21; destruct H21; elim H18; apply AxiomII; Ens.
          * apply H8 with (x:= x1); split; apply AxiomII_P; split; auto.
        + apply AxiomI; split; intros.
          * unfold Domain in H15; apply AxiomII in H15; destruct H15, H16.
            apply AxiomII_P in H16; apply H16.
          * unfold Domain; apply AxiomII; split; Ens.
            generalize (classic (z0 = x0)); intros; destruct H16.
            { exists f[z]; apply AxiomII_P; repeat split; intros; try tauto.
              apply Property_ran in H11; apply Theorem49; split; Ens. }
            { exists f[z0]; double H15; apply Theorem4' in H17; destruct H17.
              clear H18; rewrite <- H7 in H17; apply Property_Value in H17; auto.
              apply AxiomII_P; repeat split; intros; try tauto; Ens. }
        + apply AxiomI; split; intros.
          * unfold Range in H15; apply AxiomII in H15; destruct H15, H16.
            apply AxiomII_P in H16; destruct H16, H17.
            generalize (classic (x1 = x0)); intros; destruct H19.
            { apply H18 in H19; clear H18; rewrite H19; double H11.
              apply Property_ran in H18; rewrite H9, H13 in H18.
              apply Theorem4 in H18; destruct H18; auto; AssE [x0, u].
              apply Theorem49 in H20; destruct H20; apply AxiomII in H18.
              destruct H18; rewrite H22 in H11; try apply Theorem19; auto.
              elim H14; apply H8 with (x:= u); unfold Inverse.
              split; apply AxiomII_P; split; try apply Theorem49; Ens.
              apply Property_dom in H11; split; Ens. }
            { double H19; apply H18 in H20; clear H18; double H20.
              apply Property_ran in H20; rewrite H9, H13 in H20; clear H15.
              apply Theorem4 in H20; destruct H20; auto; apply AxiomII in H15.
              destruct H15; AssE [x0,u]; apply Theorem49 in H21; destruct H21.
              rewrite H20 in H18; try apply Theorem19; Ens; clear H20.
              elim H19; apply H8 with (x:= u); unfold Inverse.
              split; apply AxiomII_P; split; try apply Theorem49; Ens. }
          * unfold Range; apply AxiomII; split; Ens.
            assert (z0 ∈ ran(f)). { rewrite H9, H13; apply Theorem4; tauto. }
            unfold Range in H16; apply AxiomII in H16; destruct H16, H17.
            generalize (classic (z0 = f[z])); intros; destruct H18.
            { exists x0; apply Property_dom in H5; apply AxiomII_P.
              repeat split; intros; try tauto; try apply Theorem49; Ens.
              rewrite H7 in H5; unfold Setminus; apply Theorem4'; split; auto.
              unfold Complement; apply AxiomII; split; Ens; intro.
              unfold Singleton in H19; apply AxiomII in H19; destruct H19.
              apply Property_dom in H11; rewrite H20 in H14; try tauto.
              apply Theorem19; Ens. }
            { exists x1; apply AxiomII_P; repeat split; intros; Ens.
              - double H17; apply Property_dom in H19; rewrite H7 in H19.
                unfold Setminus; apply Theorem4'; split; auto.
                apply AxiomII; split; Ens; intro; apply AxiomII in H20.
                destruct H20; elim H18; apply H6 with (x:= z).
                rewrite H21 in H17; try split; auto; apply Theorem19.
                apply Property_dom in H11; Ens.
              - rewrite H19 in H17; add ([x0,z0] ∈ f) H5; apply H6 in H5.
                rewrite H5 in H15; generalize (Theorem101 z0); contradiction. }}
    assert (Ensemble (x ~ [z]) /\ y ⊂ (x ~ [z])).
    { split.
      - apply (Theorem33 x _); auto; unfold Included; intros.
        unfold Setminus in H15; apply Theorem4' in H15; apply H15.
      - unfold Included, Setminus; intros; apply Theorem4'; split; auto.
        unfold Complement; apply AxiomII; split; Ens; unfold Singleton; intro.
        apply AxiomII in H16; destruct H16; rewrite H17 in H15; try contradiction.
        apply Theorem19; Ens. }
    elim H15; intros; apply Theorem158 in H15; rewrite H1, H13 in H15.
    clear H17; add (Ensemble u) H16; Ens; apply Theorem154 in H16.
    apply H16 in H14; rewrite H14 in H15; clear H3 H13 H14 H16.
    unfold Finite in H; unfold W in H; apply AxiomII in H; destruct H.
    AssE u; apply Theorem132 in H5; auto.
    assert (u ∈ C). { apply Theorem164; apply AxiomII; split; auto. }
    clear H5 H13; apply Theorem156 in H14; destruct H14; rewrite H13 in H15.
    assert (u ∈ (u ∪ [u])). { apply Theorem4; right; apply AxiomII; Ens. }
    clear H5 H13; unfold PlusOne, LessEqual in H15; destruct H15.
    + generalize (Theorem102 (u ∪ [u]) u); intros; destruct H13; auto.
    + rewrite H5 in H14; generalize (Theorem101 u); contradiction.
Qed.

Hint Resolve Theorem172 : set.


(* 非有限 *)


(* 定理173 如果x是一个集，而非有限，则存在一个x的子集y使得y≠x并且x≈y *)

Lemma Lemma173 : forall x0 x,
  x0 ∈ P [x] -> ~ x0 ∈ W -> x0 ∈ (P [x] ~ W).
Proof.
  intros; unfold Setminus; apply Theorem4'; split; auto.
  unfold Complement; apply AxiomII; split; Ens.
Qed.

Theorem Theorem173 : forall x,
  Ensemble x /\ ~ Finite x -> (exists y, y ⊂ x /\ y ≠ x /\ x ≈ y).
Proof.
  intros; destruct H.
  assert (W ⊂ P[x]).
  { unfold Included; intros; double H; apply Property_PClass in H2.
    unfold W in H1; unfold C in H2; apply AxiomII in H1; apply AxiomII in H2.
    destruct H1, H2, H4; clear H5; unfold Ordinal_Number in H4; double H3.
    unfold Integer in H5; destruct H5; apply AxiomII in H4; clear H2 H6.
    destruct H4; add (Ordinal z) H4; clear H5; apply Theorem110 in H4.
    destruct H4 as [H4 | [H4 | H4]]; auto.
    - apply Theorem132 in H4; auto; destruct H0; unfold Finite.
      unfold W; apply AxiomII; split; auto.
    - destruct H0; unfold Finite; rewrite H4; apply AxiomII; Ens. }
  assert (P[x] ≈ (P[x] ~ [Φ])).
  { unfold Equivalent; exists (\{\ λ u v, u ∈ P[x] /\ ((u ∈ W -> v = PlusOne u)
    /\ (u ∈ (P[x] ~ W) -> v = u)) \}\).
    repeat split; unfold Relation; intros; try PP H2 a b; Ens.
    - destruct H2; apply AxiomII_P in H2; apply AxiomII_P in H3.
      destruct H2, H3, H4, H5; generalize (classic (x0 ∈ W)); intros; destruct H8.
      + double H8; apply H6 in H8; apply H7 in H9; rewrite H8, H9; auto.
      + apply Lemma173 in H5; auto; clear H8; double H5.
        apply H6 in H5; apply H7 in H8; rewrite H5, H8; auto.
    - destruct H2; apply AxiomII_P in H2; apply AxiomII_P in H3; destruct H2, H3.
      apply AxiomII_P in H4; apply AxiomII_P in H5; destruct H4, H5, H6, H7.
      generalize (classic (y ∈ W)) (classic (z ∈ W)); intros; destruct H10, H11.
      + apply Theorem136; auto; apply H8 in H10; apply H9 in H11.
        rewrite H10 in H11; auto.
      + double H10; apply Lemma173 in H7; auto; apply H8 in H10; apply H9 in H7.
        rewrite H7 in H10; rewrite H10 in H11; apply Theorem134 in H12; tauto.
      + double H11; apply Lemma173 in H6; auto; apply H8 in H6; apply H9 in H11.
        rewrite H6 in H11; rewrite H11 in H10; apply Theorem134 in H12; tauto.
      + apply Lemma173 in H6; apply Lemma173 in H7; auto.
        apply H8 in H6; apply H9 in H7; rewrite <- H6, <- H7; auto.
    - apply AxiomI; split; intros.
      + unfold Domain in H2; apply AxiomII in H2; destruct H2, H3.
        apply AxiomII_P in H3; apply H3.
      + unfold Domain; apply AxiomII; split; Ens.
        generalize (classic (z ∈ W)); intros; destruct H3.
        * exists (PlusOne z); apply AxiomII_P; repeat split; intros; auto.
          { apply Theorem134 in H3; apply Theorem49; split; Ens. }
          { unfold Setminus in H4; apply Theorem4' in H4; destruct H4.
            apply AxiomII in H5; destruct H5; contradiction. }
        * exists z; apply AxiomII_P; repeat split; try apply Theorem49; Ens.
          intros; contradiction.
    - apply AxiomI; split; intros.
      + unfold Range in H2; apply AxiomII in H2; destruct H2, H3.
        apply AxiomII_P in H3; destruct H3, H4.
        generalize (classic (x0 ∈ W)); intros; destruct H6.
        * double H6; apply H5 in H7; clear H5; double H6; double H6.
          apply Theorem134 in H6; apply Theorem135 in H8; rewrite H7 in *.
          clear H7; apply H1 in H6; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; apply AxiomII; split; Ens.
          intro; apply AxiomII in H7; destruct H7; rewrite H9 in H8; auto.
          apply Theorem19; Ens; exists W; apply Theorem135; auto.
        * double H4; apply Lemma173 in H7; auto; apply H5 in H7; clear H5.
          rewrite H7 in *; clear H7; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; apply AxiomII; split; Ens.
          intro; apply AxiomII in H5; clear H2; destruct H5.
          generalize (Theorem135 x0); intros; destruct H7; clear H8.
          rewrite H5 in H6; try apply Theorem19; Ens.
      + unfold Setminus in H2; apply Theorem4' in H2; destruct H2.
        unfold Complement in H3; apply AxiomII in H3; destruct H3.
        unfold Range; apply AxiomII; split; Ens.
        generalize (classic (z ∈ W)); intros; destruct H5.
        * unfold W in H5; apply AxiomII in H5; destruct H5; double H6.
          unfold Integer in H7; destruct H7, H8; clear H8.
          assert (z ⊂ z /\ z ≠ Φ).
          { split; unfold Included; intros; auto; intro; destruct H4.
            generalize (Theorem135 z); intros; destruct H4; rewrite H8.
            clear H8 H10; apply AxiomII; split; Ens. }
          apply H9 in H8; clear H9; destruct H8.
          assert (z ∈ R /\ LastMember x0 E z).
          { split; auto; try apply AxiomII; Ens. }
          apply Theorem133 in H9; unfold FirstMember in H8; destruct H8.
          AssE x0; apply Theorem132 in H8; auto; clear H10; exists x0.
          apply AxiomII_P; repeat split; intros; try apply Theorem49; Ens.
          -- apply H1; apply AxiomII; Ens.
          -- unfold Setminus in H10; apply Theorem4' in H10; destruct H10.
             unfold Complement in H12; apply AxiomII in H12; destruct H12, H13.
             unfold W; apply AxiomII; split; auto.
        * exists z; apply AxiomII_P; repeat split; try apply Theorem49; Ens.
          intros; contradiction. }
  double H; apply Theorem153 in H3; unfold Equivalent in H3.
  destruct H3 as [f H3], H3, H3, H4.
  assert (P[x] ~ [Φ] ≈ ran(f | (P[x] ~ [Φ]))).
  { unfold Equivalent; exists (f | (P[x] ~ [Φ])).
    repeat split; unfold Relation; intros; try PP H7 a b; Ens.
    - unfold Restriction in H7; apply Theorem4' in H7; destruct H7.
      PP H8 a b; Ens.
    - unfold Restriction in H7; destruct H7; apply Theorem4' in H7.
      apply Theorem4' in H8; destruct H7, H8; apply H3 with (x:= x0); auto.
    - unfold Restriction, Inverse in H7; destruct H7; apply AxiomII_P in H7.
      apply AxiomII_P in H8; destruct H7, H8; apply Theorem4' in H9.
      apply Theorem4' in H10; destruct H9, H10; apply H5 with (x:= x0).
      unfold Inverse; split; apply AxiomII_P; split; Ens.
    - apply AxiomI; split; intros.
      + unfold Domain in H7; apply AxiomII in H7; destruct H7, H8.
        unfold Restriction in H8; apply Theorem4' in H8; destruct H8.
        unfold Cartesian in H9; apply AxiomII_P in H9; apply H9.
      + unfold Domain; apply AxiomII; split; Ens; exists f[z].
        unfold Restriction; apply Theorem4'; double H7; unfold Setminus in H8.
        apply Theorem4' in H8; destruct H8; clear H9; rewrite <- H4 in H8.
        apply Property_Value in H8; auto; split; auto; unfold Cartesian.
        apply AxiomII_P; AssE ([z,f[z]]); apply Property_ran in H8.
        repeat split; Ens; apply Theorem19; Ens. }
  double H; apply Theorem153 in H8; apply Theorem146 in H8.
  apply Theorem147 with (z:= P[x] ~ [Φ]) in H8; auto; clear H2.
  apply Theorem147 with (z:= ran(f | (P[x] ~ [Φ]))) in H8; auto; clear H7.
  exists ran(f | (P[x] ~ [Φ])); repeat split; auto.
  - unfold Included; intros; unfold Range, Restriction in H2.
    apply AxiomII in H2; destruct H2, H7; apply Theorem4' in H7; destruct H7.
    apply Property_ran in H7; rewrite H6 in H7; auto.
  - generalize (Theorem135 x); intros; destruct H2; clear H7; apply H1 in H2.
    rewrite <- H4 in H2; apply Property_Value in H2; auto; intro.
    assert (f[Φ] ∈ ran(f | (P[x] ~ [Φ]))).
    { rewrite H7; apply Property_ran in H2; rewrite H6 in H2; auto. }
    unfold Range in H9; apply AxiomII in H9; destruct H9, H10.
    unfold Restriction in H10; apply Theorem4' in H10; destruct H10.
    assert ([f[Φ],Φ] ∈ f⁻¹ /\ [f[Φ],x0] ∈ f⁻¹).
    { AssE [Φ,f[Φ]]; AssE [x0,f[Φ]]; apply Theorem49 in H12.
      apply Theorem49 in H13; destruct H12, H13; clear H14 H15.
      split; apply AxiomII_P; split; try apply Theorem49; auto. }
    apply H5 in H12; rewrite H12 in H11; clear H12; unfold Cartesian in H11.
    apply AxiomII_P in H11; destruct H11, H12; clear H11 H13.
    unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
    unfold Complement in H12; apply AxiomII in H12; destruct H12, H13.
    unfold Singleton; apply AxiomII; split; Ens.
Qed.

Hint Resolve Theorem173 : set.


(* 定理174 如果x∈(R~w)，则P[x+1]=P[x] *)

Lemma Lemma174 : forall x y, x ≼ y -> y ≼ x -> x = y.
Proof.
  intros; unfold LessEqual in H, H0; destruct H, H0; auto.
  generalize (Theorem102 x y); intros; destruct H1; auto.
Qed.

Theorem Theorem174 : forall x,
  x ∈ (R ~ W) -> P[ PlusOne x ] = P[x].
Proof.
  intros.
  unfold Setminus in H; apply Theorem4' in H; destruct H.
  double H; apply Lemma123 in H1; AssE (PlusOne x).
  add (x⊂(PlusOne x)) H2; try (unfold Included; intros; apply Theorem4; tauto).
  apply Theorem158 in H2; apply AxiomII in H0; destruct H0.
  assert (Ensemble x /\ ~ Finite x).
  { split; auto; clear H1 H2; unfold Finite; intro; destruct H3.
    generalize (Property_W); intros; unfold R in H; apply AxiomII in H.
    clear H0; destruct H; assert (Ordinal W /\ Ordinal x); auto; double H3.
    apply Theorem110 in H3; apply Theorem118 in H4.
    destruct H3 as [H3 | [H3 | H3]]; auto.
    - assert (W ≼ x); unfold LessEqual; try tauto; apply H4 in H5; clear H4.
      assert (Ensemble x /\ W ⊂ x); auto; apply Theorem158 in H4.
      double H1; unfold W in H6; apply AxiomII in H6; destruct H6.
      unfold Integer in H7; destruct H7; clear H8.
      assert (Ordinal P[x] /\ Ordinal W); auto; apply Theorem118 in H8.
      assert (P[x] ≼ W); unfold LessEqual; try auto; apply H8 in H9; clear H8.
      assert (Ensemble W /\ P [x] ⊂ W); Ens; apply Theorem158 in H8; clear H9.
      rewrite Theorem155 in H8. apply Lemma174 in H8; auto.
      rewrite <- H8 in H1; clear H4 H8; generalize Theorem165; intros.
      apply Theorem156 in H4; destruct H4; rewrite H8 in H1.
      generalize (Theorem101 W); intros; contradiction.
    - rewrite H3 in H1; generalize Theorem165; intros; rewrite H3 in H5.
      apply Theorem156 in H5; destruct H5; rewrite H6 in H1.
      generalize (Theorem101 x); intros; contradiction. }
  apply Theorem173 in H4; destruct H4 as [u H4], H4, H5.
  assert (P[PlusOne x] ≼ P[x]).
  { assert (u ⊊ x). { split; auto. } apply Property_ProperSubset' in H7.
    destruct H7 as [z H7], H7, H6 as [f H6], H6, H6, H9.
    assert (PlusOne x ≈ ran(\{\ λ v w, (v∈x /\ w=f[v]) \/ (v=x /\ w=z) \}\)).
    { unfold Equivalent; exists (\{\λ v w, (v∈x /\ w=f[v]) \/ (v=x /\ w=z)\}\).
      repeat split; unfold Relation; intros; try PP H12 a b; Ens.
      - destruct H12; apply AxiomII_P in H12; apply AxiomII_P in H13.
        destruct H12, H13, H14, H15, H14, H15; try rewrite H16, H17; auto.
        + rewrite H15 in H14; generalize (Theorem101 x); contradiction.
        + rewrite H14 in H15; generalize (Theorem101 x); contradiction.
      - destruct H12; apply AxiomII_P in H12; apply AxiomII_P in H13.
        destruct H12, H13; apply AxiomII_P in H14; apply AxiomII_P in H15.
        destruct H14, H15, H16, H17, H16, H17.
        + rewrite <- H9 in H16, H17; apply Property_Value in H16; auto.
          apply Property_Value in H17; auto; rewrite H19 in *; clear H19.
          rewrite H18 in *; clear H18; apply H10 with (x:= f[y]).
          unfold Inverse; split; apply AxiomII_P; Ens.
        + rewrite <- H9 in H16; apply Property_Value in H16; auto.
          apply Property_ran in H16; rewrite H11 in H16; rewrite <- H18 in H16.
          rewrite H19 in H16; contradiction.
        + rewrite <- H9 in H17; apply Property_Value in H17; auto.
          apply Property_ran in H17; rewrite H11 in H17; rewrite <- H19 in H17.
          rewrite H18 in H17; contradiction.
        + rewrite H16, H17; auto.
      - apply AxiomI; split; intros.
        + unfold PlusOne; apply Theorem4; unfold Domain in H12.
          apply AxiomII in H12; destruct H12, H13; apply AxiomII_P in H13.
          destruct H13, H14; destruct H14; try tauto; rewrite H14 in *.
          right; unfold Singleton; apply AxiomII; split; Ens.
        + unfold Domain; apply AxiomII; split; Ens; unfold PlusOne in H12.
          apply Theorem4 in H12; destruct H12.
          * double H12; rewrite <- H9 in H13; apply Property_Value in H13; auto.
            exists f[z0]; apply AxiomII_P; repeat split; intros; Ens.
          * exists z; apply AxiomII_P; split; try apply Theorem49; Ens.
            right; split; auto; unfold Singleton in H12; apply AxiomII in H12.
            apply H12; apply Theorem19; auto. }
    assert (Ensemble x /\ ran(\{\λ v w, (v∈x/\w=f[v]) \/ (v=x/\w=z) \}\) ⊂ x).
    { split; auto; unfold Included; intros; apply AxiomII in H13.
      destruct H13, H14; apply AxiomII_P in H14; destruct H14, H15, H15.
      - rewrite H16; rewrite <- H9 in H15; apply Property_Value in H15; auto.
        apply Property_ran in H15; rewrite H11 in H15; auto.
      - rewrite H16; auto. }
    clear H0; elim H13; intros; apply Theorem158 in H13.
    apply Theorem154 in H12; try (split; Ens; apply (Theorem33 x _); auto).
    rewrite <- H12 in H13; clear H12 H14; auto. }
  apply Lemma174; auto.
Qed.

Hint Resolve Theorem174 : set.


(* 定义175 max[x,y]=x∪y *)

Definition Max x y : Class := x ∪ y.

Corollary Property_Max : forall x y,
  (Ordinal x -> Ordinal y -> x ∈ y -> Max x y = y) /\ (x = y -> Max x y = y).
Proof.
  split; intros; try (rewrite H; unfold Max; apply Theorem5).
  assert (x ≼ y); unfold LessEqual; try tauto.
  apply Theorem118 in H2; auto; unfold Max; apply Theorem29; auto.
Qed.

Corollary Equal_Max : forall x y, Max x y = Max y x.
Proof.
  intros; unfold Max; apply Theorem6.
Qed.

Hint Unfold Max : set.


(* 定义176 《 = {z:对于在R×R中的某个[u,v]与在R×R中的某个[x,y],z=[(u,v],[x,y]),且max[u,v]<max[x,y],或者max[u,v]=max[x,y]且u<x,或者max[u,v]=max[x,y]且u=x和v<y} *)

Definition LessLess : Class :=
  \{ λ z, exists u v x y, [u,v]∈(R×R) /\ [x,y]∈(R×R) /\ z = [[u,v],[x,y]] /\
  ((Max u v ≺ Max x y) \/ (Max u v = Max x y /\ u ≺ x) \/ (Max u v = Max x y /\
  u = x /\ v ≺ y)) \}.

Notation "≪" := (LessLess) (at level 0, no associativity).

Hint Unfold LessLess : set.


(* 定理177 《 良序 R×R *)

Definition En_y y : Class := \{ λ z, exists u v, [u,v] ∈ y /\ z = Max u v \}.

Definition En_v v y : Class := \{ λ z, [z,v] ∈ y /\ z ∈ v \}.

Definition En_u u y : Class := \{ λ z, [u,z] ∈ y /\ z ∈ u \}.

Lemma Lemma177_bd : forall a b c d,
  [a, b] ∈ R × R -> [c, d] ∈ R × R -> Ensemble a -> Ensemble b ->
  Ensemble c -> Ensemble d -> Ordinal a -> Ordinal b -> Ordinal c ->
  Ordinal d -> Max a b = b -> Max c d = d ->
  Rrelation ([a,b]) ≪ ([c,d]) \/ Rrelation ([c,d]) ≪ ([a,b]) \/ [a,b] = [c,d].
Proof.
  intros.
  assert (Ordinal b /\ Ordinal d); auto; apply Theorem110 in H11.
  destruct H11 as [H11 | [H11 | H11]].
  - left; unfold Rrelation, LessLess; apply AxiomII.
    split; try (apply Theorem49; split; apply Theorem49; auto).
    exists a, b, c, d; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - right; left; unfold Rrelation, LessLess; apply AxiomII.
    split; try (apply Theorem49; split; apply Theorem49; auto).
    exists c, d, a, b; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - assert (Ordinal a /\ Ordinal c); auto; apply Theorem110 in H12.
    destruct H12 as [H12 | [H12 | H12]].
    { left; unfold Rrelation, LessLess; apply AxiomII.
      split; try (apply Theorem49; split; apply Theorem49; auto).
      exists a, b, c, d; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; left; unfold Rrelation, LessLess; apply AxiomII.
      split; try (apply Theorem49; split; apply Theorem49; auto).
      exists c, d, a, b; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; right; rewrite H11, H12; auto. }
Qed.

Lemma Lemma177_bc : forall a b c d,
  [a, b] ∈ R × R -> [c, d] ∈ R × R -> Ensemble a -> Ensemble b ->
  Ensemble c -> Ensemble d -> Ordinal a -> Ordinal b -> Ordinal c ->
  Ordinal d -> Max a b = b -> Max c d = c ->
  Rrelation ([a,b]) ≪ ([c,d]) \/ Rrelation ([c,d]) ≪ ([a,b]) \/ [a,b] = [c,d].
Proof.
  intros; assert (Ordinal b /\ Ordinal c); auto.
  apply Theorem110 in H11; destruct H11 as [H11 | [H11 | H11]].
  - left; unfold Rrelation, LessLess; apply AxiomII.
    split; try (apply Theorem49; split; apply Theorem49; auto).
    exists a, b, c, d; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - right; left; unfold Rrelation, LessLess; apply AxiomII.
    split; try (apply Theorem49; split; apply Theorem49; auto).
    exists c, d, a, b; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - assert (Ordinal a /\ Ordinal c); auto; apply Theorem110 in H12.
    destruct H12 as [H12 | [H12 | H12]].
    { left; unfold Rrelation, LessLess; apply AxiomII.
      split; try (apply Theorem49; split; apply Theorem49; auto).
      exists a, b, c, d; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; left; unfold Rrelation, LessLess; apply AxiomII.
      split; try (apply Theorem49; split; apply Theorem49; auto).
      exists c, d, a, b; repeat split; auto; right; left.
      rewrite H9, H10; unfold Less; split; auto. }
    { assert (Ordinal b /\ Ordinal d); auto; apply Theorem110 in H13.
      destruct H13 as [H13 | [H13 | H13]].
      - left; unfold Rrelation, LessLess; apply AxiomII.
        split; try (apply Theorem49; split; apply Theorem49; auto).
        exists a, b, c, d; repeat split; auto; right; right.
        rewrite H9, H10; unfold Less; auto.
      - right; left; unfold Rrelation, LessLess; apply AxiomII.
        split; try (apply Theorem49; split; apply Theorem49; auto).
        exists c, d, a, b; repeat split; auto; right; right.
        rewrite H9, H10; unfold Less; auto.
      - right; right; rewrite H12, H13; auto. }
Qed.

Lemma Lemma177_ac : forall a b c d,
  [a, b] ∈ R × R -> [c, d] ∈ R × R -> Ensemble a -> Ensemble b ->
  Ensemble c -> Ensemble d -> Ordinal a -> Ordinal b -> Ordinal c ->
  Ordinal d -> Max a b = a -> Max c d = c ->
  Rrelation ([a,b]) ≪ ([c,d]) \/ Rrelation ([c,d]) ≪ ([a,b]) \/ [a,b] = [c,d].
Proof.
  intros; assert (Ordinal a /\ Ordinal c); auto.
  apply Theorem110 in H11; destruct H11 as [H11 | [H11 | H11]].
  - left; unfold Rrelation, LessLess; apply AxiomII.
    split; try (apply Theorem49; split; apply Theorem49; auto).
    exists a, b, c, d; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - right; left; unfold Rrelation, LessLess; apply AxiomII.
    split; try (apply Theorem49; split; apply Theorem49; auto).
    exists c, d, a, b; repeat split; auto; left.
    rewrite H9, H10; unfold Less; auto.
  - assert (Ordinal b /\ Ordinal d); auto; apply Theorem110 in H12.
    destruct H12 as [H12 | [H12 | H12]].
    { left; unfold Rrelation, LessLess; apply AxiomII.
      split; try (apply Theorem49; split; apply Theorem49; auto).
      exists a, b, c, d; repeat split; auto; right; right.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; left; unfold Rrelation, LessLess; apply AxiomII.
      split; try (apply Theorem49; split; apply Theorem49; auto).
      exists c, d, a, b; repeat split; auto; right; right.
      rewrite H9, H10; unfold Less; split; auto. }
    { right; right; rewrite H11, H12; auto. }
Qed.

Lemma Lemma177_v : forall x y u v,
  x ∈ y -> y ⊂ (R × R) -> Max u v = v -> Rrelation x ≪ ([u,v]) ->
  (exists a b, [a, b] ∈ y /\ Ensemble a /\ Ordinal a /\ Ensemble b /\ Ordinal b
  /\ ((Max a b) ∈ v \/ Max a b = v /\ a ∈ u \/ Max a b = v /\ a = u /\ b ∈ v)).
Proof.
  intros.
  double H; apply H0 in H3; unfold Cartesian in H3; clear H0.
  PP H3 a b; apply AxiomII_P in H0; clear H3; exists a, b; split; auto.
  destruct H0, H3; apply AxiomII in H3; apply AxiomII in H4; clear H0.
  destruct H3, H4; unfold Rrelation, LessLess in H2; apply AxiomII in H2.
  destruct H2, H6, H6, H6, H6, H6, H7, H8; clear H6 H7; apply Theorem49 in H2.
  destruct H2; clear H2; apply Theorem49 in H6; destruct H6; unfold Less in H9.
  apply Theorem55 in H8; try (split; Ens; apply Theorem49; Ens).
  destruct H8; apply Theorem55 in H7; apply Theorem55 in H8; auto.
  destruct H7, H8; rewrite <- H7, <- H8, <- H10, <- H11, H1 in H9; Ens.
Qed.

Lemma Lemma177_u : forall x y u v,
  x ∈ y -> y ⊂ (R × R) -> Max u v = u -> Rrelation x ≪ ([u,v]) ->
  (exists a b, [a, b] ∈ y /\ Ensemble a /\ Ordinal a /\ Ensemble b /\ Ordinal b
  /\ ((Max a b) ∈ u \/ Max a b = u /\ a ∈ u \/ Max a b = u /\ a = u /\ b ∈ v)).
Proof.
  intros.
  double H; apply H0 in H3; unfold Cartesian in H3; clear H0.
  PP H3 a b; apply AxiomII_P in H0; clear H3; exists a, b; split; auto.
  destruct H0, H3; apply AxiomII in H3; apply AxiomII in H4; clear H0.
  destruct H3, H4; unfold Rrelation, LessLess in H2; apply AxiomII in H2.
  destruct H2, H6, H6, H6, H6, H6, H7, H8; clear H6 H7; apply Theorem49 in H2.
  destruct H2; clear H2; apply Theorem49 in H6; destruct H6; unfold Less in H9.
  apply Theorem55 in H8; try (split; Ens; apply Theorem49; Ens).
  destruct H8; apply Theorem55 in H7; apply Theorem55 in H8; auto.
  destruct H7, H8; rewrite <- H7, <- H8, <- H10, <- H11, H1 in H9; Ens.
Qed.

Theorem Theorem177 : WellOrdered ≪ (R × R).
Proof.
  unfold WellOrdered; split; intros.
  - unfold Connect; intros; destruct H; double H; double H0; PP H1 a b.
    PP H2 c d; clear H1 H2; apply AxiomII_P in H3; apply AxiomII_P in H4.
    destruct H3, H4; clear H1 H3; destruct H2, H4; unfold R in H1, H2, H3, H4.
    apply AxiomII in H1; apply AxiomII in H2; apply AxiomII in H3.
    apply AxiomII in H4; destruct H1, H2, H3, H4.
    assert (Ordinal a /\ Ordinal b); assert (Ordinal c /\ Ordinal d); auto.
    apply Theorem110 in H9; apply Theorem110 in H10.
    destruct H9 as [H9 | [H9 | H9]], H10 as [H10 | [H10 | H10]];
    apply Property_Max in H9; apply Property_Max in H10; auto.
    + apply Lemma177_bd; auto.
    + rewrite Equal_Max in H10; apply Lemma177_bc; auto.
    + apply Lemma177_bd; auto.
    + rewrite Equal_Max in H9; apply (Lemma177_bc c d a b) in H10; auto.
      destruct H10 as [H10 | [H10| H10]]; try rewrite H10; auto.
    + rewrite Equal_Max in H9, H10; apply Lemma177_ac; auto.
    + rewrite Equal_Max in H9; apply (Lemma177_bc c d a b) in H10; auto.
      destruct H10 as [H10 | [H10| H10]]; try rewrite H10; auto.
    + apply Lemma177_bd; auto.
    + rewrite Equal_Max in H10; apply Lemma177_bc; auto.
    + apply Lemma177_bd; auto.
  - destruct H.
    assert ((En_y y) ⊂ R /\ (En_y y) ≠ Φ).
    { split.
      - unfold Included; intros; apply AxiomII in H1; destruct H1, H2, H2, H2.
        apply H in H2; apply AxiomII_P in H2; destruct H2, H4; clear H2.
        apply AxiomII in H4; apply AxiomII in H5; destruct H4, H5.
        assert (Ordinal x /\ Ordinal x0); auto; apply Theorem110 in H7.
        rewrite H3; destruct H7 as [H7|[H7|H7]]; apply Property_Max in H7; auto;
        try (rewrite H7; unfold R; apply AxiomII; Ens).
        rewrite Equal_Max in H7; rewrite H7; apply AxiomII; Ens.
      - apply Lemma35 in H0; destruct H0; double H0; apply H in H1; PP H1 a b.
        apply AxiomII_P in H2; clear H1; destruct H2, H2; clear H1.
        apply AxiomII in H2; apply AxiomII in H3; destruct H2, H3; apply Lemma35.
        assert (Ordinal a /\ Ordinal b); auto; apply Theorem110 in H5.
        destruct H5 as [H5|[H5|H5]]; apply Property_Max in H5; auto.
        + exists b; apply AxiomII; split; auto; exists a, b; auto.
        + exists a; apply AxiomII; split; auto; exists a, b; split; auto.
          rewrite Equal_Max; symmetry; auto.
        + exists b; apply AxiomII; split; auto; exists a, b; auto. }
    clear H0; apply Lemma121 in H1; unfold FirstMember in H1; destruct H1.
    apply AxiomII in H0; destruct H0, H2 as [u [v H2]], H2.
    generalize (classic ((En_v (∩ En_y y) y) = Φ)); intros; destruct H4.
    + generalize (classic ((En_u (∩ En_y y) y) = Φ)); intros; destruct H5.
      * double H2; apply H in H6; unfold Cartesian in H6; apply AxiomII_P in H6.
        destruct H6, H7; apply AxiomII in H7; apply AxiomII in H8; clear H6.
        destruct H7, H8; assert (Ordinal u /\ Ordinal v); auto.
        apply Theorem110 in H10; destruct H10 as [H10 | [H10 | H10]].
        { double H10; apply Property_Max in H11; auto.
          rewrite H11 in H3; rewrite H3 in *; clear H3 H11.
          assert (u ∈ (En_v v y)); try (apply AxiomII; Ens); rewrite H4 in H3.
          generalize (Theorem16 u); intros; contradiction. }
        { double H10; apply Property_Max in H11; auto; rewrite Equal_Max in H11.
          rewrite H11 in H3; rewrite H3 in *; clear H3 H11.
          assert (v ∈ (En_u u y)); try (apply AxiomII; Ens); rewrite H5 in H3.
          generalize (Theorem16 v); intros; contradiction. }
        { double H10; apply Property_Max in H11; rewrite H11 in H3.
          rewrite H3, H10 in *; clear H3 H6 H8 H9 H10; exists [v,v].
          unfold FirstMember; split; auto; intros; intro.
          apply Lemma177_v with (y:= y) in H6; auto; clear H3 H11.
          destruct H6 as [a [b H6]], H6, H6, H8, H9, H10.
          assert (Ordinal a /\ Ordinal b); auto; apply Theorem110 in H12.
          destruct H12 as [H12 | [H12 | H12]].
          - apply Property_Max in H12; auto; rewrite H12 in H11.
            destruct H11 as [H11 | [H11 | H11]].
            + assert (b ∈ (En_y y)); try apply AxiomII; Ens.
              apply H1 in H13; elim H13; clear H12 H13; unfold Rrelation, E.
              apply AxiomII_P; split; try apply Theorem49; auto.
            + destruct H11; rewrite H11 in *; clear H9 H10 H11.
              assert (a ∈ (En_v v y)); try apply AxiomII; Ens.
              rewrite H4 in H9; generalize (Theorem16 a); contradiction.
            + destruct H11, H13; rewrite H11 in H14.
              generalize (Theorem101 v); intros; contradiction.
          - apply Property_Max in H12; auto; rewrite Equal_Max in H12.
            rewrite H12 in H11; destruct H11 as [H11 | [H11 | H11]].
            + assert (a ∈ (En_y y)); try apply AxiomII; Ens.
              apply H1 in H13; elim H13; clear H12 H13; unfold Rrelation, E.
              apply AxiomII_P; split; try apply Theorem49; auto.
            + destruct H11; rewrite H11 in H13.
              generalize (Theorem101 v); intros; contradiction.
            + destruct H11; clear H11; destruct H13; rewrite H11 in *.
              clear H11 H12; assert (b ∈ (En_u v y)); try apply AxiomII; Ens.
              rewrite H5 in H11; generalize (Theorem16 b); contradiction.
          - double H12; apply Property_Max in H13; auto; rewrite H13 in H11.
            rewrite H12 in *; clear H9 H10 H12; destruct H11 as [H9|[H9|H9]].
            + assert (b ∈ (En_y y)); try apply AxiomII; Ens.
              apply H1 in H10; elim H10; clear H13 H10; unfold Rrelation, E.
              apply AxiomII_P; split; try apply Theorem49; auto.
            + destruct H9; rewrite H9 in H10.
              generalize (Theorem101 v); intros; contradiction.
            + destruct H9, H10; rewrite H9 in H11.
              generalize (Theorem101 v); intros; contradiction. }
      * assert ((En_u (∩ En_y y) y) ⊂ R /\ (En_u (∩ En_y y) y) ≠ Φ).
        { split; auto; unfold Included; intros; apply AxiomII in H6.
          destruct H6, H7; apply H in H7; apply AxiomII_P in H7; apply H7. }
        apply Lemma121 in H6; clear H5; destruct H6; apply AxiomII in H5.
        destruct H5, H7; exists [∩ (En_y y), ∩ (En_u (∩(En_y y)) y)].
        clear H5; double H7; apply H in H7; apply AxiomII_P in H7.
        destruct H7; clear H7; destruct H9; apply AxiomII in H7.
        apply AxiomII in H9; clear H0; destruct H7, H9.
        double H8; apply Property_Max in H11; auto.
        unfold FirstMember; split; auto; intros; intro.
        apply Lemma177_u with (y:= y) in H13; try rewrite Equal_Max; auto.
        clear H12; destruct H13 as [a [b H13]], H13, H13, H14, H15, H16.
        assert (Ordinal a /\ Ordinal b); auto; apply Theorem110 in H18.
        destruct H18 as [H18 | [H18 | H18]].
        { double H18; apply Property_Max in H19; auto; rewrite H19 in H17.
          destruct H17 as [H17 | [H17 | H17]].
          - assert (b ∈ (En_y y)); try apply AxiomII; Ens.
            apply H1 in H20; elim H20; clear H19 H20; unfold Rrelation, E.
            apply AxiomII_P; split; try apply Theorem49; auto.
          - destruct H17; rewrite H17 in *; clear H15 H16 H17.
            assert (a ∈ (En_v (∩ En_y y) y)); try apply AxiomII; Ens.
            rewrite H4 in H15; generalize (Theorem16 a); contradiction.
          - destruct H17, H20; rewrite <- H17 in H20; rewrite H20 in H18.
            generalize (Theorem101 b); intros; contradiction. }
        { double H18; apply Property_Max in H19; auto; rewrite Equal_Max in H19.
          rewrite H19 in H17; destruct H17 as [H17 | [H17 | H17]].
          - assert (a ∈ (En_y y)); try apply AxiomII; Ens.
            apply H1 in H20; elim H20; clear H19 H20; unfold Rrelation, E.
            apply AxiomII_P; split; try apply Theorem49; auto.
          - destruct H17; rewrite <- H17 in H20.
            generalize (Theorem101 a); intros; contradiction.
          - destruct H17; clear H17; destruct H20; rewrite H17 in *.
            assert (b∈(En_u (∩ En_y y) y)); try apply AxiomII; Ens.
            apply H6 in H21. elim H21; unfold Rrelation, E.
            apply AxiomII_P; split; try apply Theorem49; auto. }
        { double H18; apply Property_Max in H19; rewrite H19 in H17.
          rewrite H18 in *; clear H15 H16 H18; destruct H17 as [H15|[H15|H15]].
          - assert (b ∈ (En_y y)); try apply AxiomII; Ens.
            apply H1 in H16; elim H16; clear H19 H16; unfold Rrelation, E.
            apply AxiomII_P; split; try apply Theorem49; auto.
          - destruct H15; rewrite <- H15 in H16.
            generalize (Theorem101 b); intros; contradiction.
          - destruct H15; clear H15; destruct H16; rewrite H15 in H16.
            generalize (Theorem102 (∩ En_y y) (∩ En_u (∩ En_y y) y)); intros.
            destruct H17; split; auto. }
    + assert ((En_v (∩ En_y y) y) ⊂ R /\ (En_v (∩ En_y y) y) ≠ Φ).
      { split; auto; unfold Included; intros; apply AxiomII in H5.
        destruct H5, H6; apply H in H6; apply AxiomII_P in H6; apply H6. }
      apply Lemma121 in H5; clear H4; destruct H5; apply AxiomII in H4.
      destruct H4, H6; exists [∩ (En_v (∩ En_y y) y), ∩ (En_y y)].
      clear H4; double H6; apply H in H6; apply AxiomII_P in H6; destruct H6.
      clear H6; destruct H8; apply AxiomII in H6; apply AxiomII in H8.
      clear H0; destruct H6, H8; double H7; apply Property_Max in H10; auto.
      unfold FirstMember; split; auto; intros; intro.
      apply Lemma177_v with (y:= y) in H12; auto; clear H11.
      destruct H12 as [a [b H12]], H12, H12, H13, H14, H15.
      assert (Ordinal a /\ Ordinal b); auto; apply Theorem110 in H17.
      destruct H17 as [H17 | [H17 | H17]].
      { double H17; apply Property_Max in H18; auto; rewrite H18 in H16.
        destruct H16 as [H16 | [H16 | H16]].
        - assert (b ∈ (En_y y)); try apply AxiomII; Ens.
          apply H1 in H19; elim H19; clear H18 H19; unfold Rrelation, E.
          apply AxiomII_P; split; try apply Theorem49; auto.
        - destruct H16; rewrite H16 in *; clear H14 H15 H16.
          assert (a ∈ (En_v (∩ En_y y) y)); try apply AxiomII; Ens.
          apply H5 in H14; destruct H14; unfold Rrelation, E.
          apply AxiomII_P; split; try apply Theorem49; auto.
        - destruct H16, H19; rewrite <- H16 in H20.
          generalize (Theorem101 b); intros; contradiction. }
      { double H17; apply Property_Max in H18; auto; rewrite Equal_Max in H18.
        rewrite H18 in H16; destruct H16 as [H16 | [H16 | H16]].
        - assert (a ∈ (En_y y)); try apply AxiomII; Ens.
          apply H1 in H19; destruct H19; unfold Rrelation, E.
          apply AxiomII_P; split; try apply Theorem49; auto.
        - destruct H16; rewrite H16 in H19.
          generalize (Theorem102 (∩ En_y y) (∩ En_v (∩ En_y y) y)); intros.
          destruct H20; split; auto.
        - destruct H16, H19; rewrite <- H19, <- H16 in H7.
          generalize (Theorem101 a); intros; contradiction. }
      { double H17; apply Property_Max in H18; rewrite H18 in H16.
        rewrite H17 in *; clear H14 H15 H17; destruct H16 as [H14|[H14|H14]].
        - assert (b ∈ (En_y y)); try apply AxiomII; Ens.
          apply H1 in H15; destruct H15; unfold Rrelation, E.
          apply AxiomII_P; split; try apply Theorem49; auto.
        - destruct H14; rewrite <- H14 in *.
          generalize (Theorem102 b (∩ En_v b y)); intros; destruct H16; auto.
        - destruct H14, H15; rewrite <- H15, <- H14 in H7.
          generalize (Theorem101 b); intros; contradiction. }
Qed.

Hint Resolve Theorem177 : set.


(* 定理178 如果[u,v]《[x,y]，则[u,v]∈(max[x,y]+1)×(max[x,y]+1) *)

Theorem Theorem178 : forall u v x y,
  Rrelation ([u,v]) ≪ ([x,y]) ->
  [u,v] ∈ ((PlusOne (Max x y)) × (PlusOne (Max x y))).
Proof.
  intros.
  unfold Rrelation, LessLess in H; apply AxiomII in H.
  destruct H, H0, H0, H0, H0, H0, H1, H2; apply Theorem49 in H; destruct H.
  apply Theorem55 in H2; auto; destruct H2; apply Theorem49 in H.
  apply Theorem49 in H4; destruct H, H4; apply Theorem55 in H2; auto.
  apply Theorem55 in H5; auto; destruct H2, H5; rewrite <- H2, <- H5 in *.
  rewrite <- H8, <- H9 in *; clear H H2 H4 H5 H6 H7 H8 H9 x0 x1 x2 x3.
  assert ((Max u v) ≼ (Max x y)).
  { unfold LessEqual; destruct H3 as [H3|[H3|H3]]; try tauto. }
  clear H3; unfold Cartesian in H0, H1; apply AxiomII_P in H0.
  apply AxiomII_P in H1; destruct H0, H1, H2, H3; unfold R in H2, H3, H4, H5.
  clear H0 H1; apply AxiomII in H2; apply AxiomII in H3; apply AxiomII in H4.
  apply AxiomII in H5; destruct H2, H3, H4, H5, H.
  - assert ((Max x y) ∈ R).
    { assert (Ordinal x /\ Ordinal y); auto; apply Theorem110 in H8.
      destruct H8 as [H8|[H8|H8]]; apply Property_Max in H8; auto; try rewrite H8.
      - unfold R; apply AxiomII; split; auto.
      - rewrite Equal_Max in H8; rewrite H8; unfold R; apply AxiomII; auto.
      - unfold R; apply AxiomII; split; auto. }
    double H8; apply Lemma123 in H9; unfold R in H8, H9; apply AxiomII in H8.
    apply AxiomII in H9; destruct H8, H9; unfold LessEqual in H.
    assert ((Max x y) ∈ (PlusOne (Max x y))).
    { unfold PlusOne; apply Theorem4; right; apply AxiomII; split; auto. }
    unfold Ordinal, full in H11; destruct H11 as [_ H11]; apply H11 in H12.
    apply H12 in H; clear H8 H9 H10 H12; assert (Ordinal u /\ Ordinal v); auto.
    apply Theorem110 in H8; destruct H8 as [H8 | [H8 | H8]].
    + double H8; apply Property_Max in H9; auto; rewrite H9 in H; clear H9.
      double H; apply H11 in H9; apply H9 in H8; clear H9 H11; unfold Cartesian.
      apply AxiomII_P; repeat split; try apply Theorem49; auto.
    + double H8; apply Property_Max in H9; auto; rewrite Equal_Max in H9.
      rewrite H9 in H; clear H9; double H; apply H11 in H9; apply H9 in H8.
      clear H9 H11; unfold Cartesian; apply AxiomII_P.
      repeat split; try apply Theorem49; auto.
    + double H8; apply Property_Max in H9; auto; rewrite H9 in H; rewrite H8.
      clear H8 H9 H11; apply AxiomII_P; repeat split; try apply Theorem49; auto.
  - rewrite <- H in *; clear H; assert (Ordinal u /\ Ordinal v); auto.
    apply Theorem110 in H; destruct H as [H | [H | H]].
    + double H; apply Property_Max in H8; auto; rewrite H8; clear H8.
      unfold Cartesian; apply AxiomII_P; repeat split; try apply Theorem49; auto.
      * apply Theorem4; tauto.
      * apply Theorem4; right; apply AxiomII; auto.
    + double H; apply Property_Max in H8; auto; rewrite Equal_Max in H8.
      rewrite H8; clear H8; unfold Cartesian; apply AxiomII_P.
      repeat split; try apply Theorem49; auto; try (apply Theorem4; tauto).
      apply Theorem4; right; apply AxiomII; auto.
    + double H; apply Property_Max in H8; rewrite H8; clear H8; rewrite H at 1.
      unfold Cartesian; apply AxiomII_P; split; try apply Theorem49; auto.
      split; apply Theorem4; right; apply AxiomII; auto.
Qed.

Hint Resolve Theorem178 : set.


(* 定理179 如果x∈(C~w)，则P(x×x)=x *)

Theorem Theorem179 : forall x, x ∈ (C ~ W) -> P[x × x] = x.
Proof.
  intros.
  generalize Theorem150; intros.
  unfold WellOrdered in H0; destruct H0; clear H0.
  generalize (classic (\{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \} = Φ)); intros.
  destruct H0.
  - generalize (classic (P[x × x] = x)); intros; destruct H2; auto.
    assert (x ∈ Φ). { rewrite <- H0; apply AxiomII; Ens. }
    generalize (Theorem16 x); intros; contradiction.
  - assert (\{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \} ⊂ C /\
            \{ λ z, z ∈ (C ~ W) /\ P[z × z] <> z \} ≠ Φ).
    { split; auto; unfold Included; intros; apply AxiomII in H2.
      destruct H2, H3; apply Theorem4' in H3; apply H3. }
    apply H1 in H2; clear H0 H1; destruct H2; unfold FirstMember in H0.
    destruct H0; apply AxiomII in H0; destruct H0, H2.
    generalize Theorem177, Theorem113; intros; destruct H5.
    assert (Ensemble x0 /\ Ensemble x0); Ens; apply Theorem74 in H7.
    assert (x0 × x0 ⊂ R × R).
    { unfold Setminus in H2; apply Theorem4' in H2; destruct H2 as [H2 _].
      unfold C in H2; apply AxiomII in H2; destruct H2 as [_ H2].
      destruct H2 as [H2 _]; unfold Ordinal_Number in H2; unfold Ordinal in H5.
      destruct H5 as [_ H5]; apply H5 in H2; clear H5.
      unfold Cartesian, Included; intros; PP H5 a b; apply AxiomII_P in H8.
      destruct H8, H9; apply H2 in H9; apply H2 in H10; apply AxiomII_P; Ens. }
    apply Lemma97 with (y:= x0 × x0) in H4; auto; clear H8.
    apply Theorem107 in H5; add (WellOrdered E R) H4; auto; clear H5.
    apply Theorem100 in H4; auto; clear H6 H7; destruct H4 as [f H4], H4, H5.
    unfold Order_PXY in H5; destruct H5, H7, H8; clear H4 H5 H7; destruct H9.
    apply Theorem96 in H8; destruct H8 as [H7 _].
    assert (forall u v, [u,v] ∈ (x0 × x0) -> f[[u,v]] ∈ x0).
    { intros; generalize (classic (x0 = W)); intros; destruct H9.
      - rewrite H9 in *; clear H9; apply AxiomII; destruct H7; clear H9.
        double H8; rewrite <- H6 in H9; apply Property_Value in H9; auto.
        apply Property_ran in H9; split; Ens; unfold Integer.
    
    assert (P[dom(f)] = P[ran(f)]).
    { apply Theorem154; unfold Equivalent. 
      - destruct H7; assert (Ensemble x0 /\ Ensemble x0); auto.
        apply Theorem74 in H9; rewrite <- H6 in H9; split; auto.
        apply AxiomV; auto.
      - exists f; repeat split; try apply H7. }
    assert ( P[x0 × x0] ≼ x0 ).
    { rewrite <- H6, H8.
    = -> FirstMember contradiction
    < -> Property P(x * x) => P(x) (find P(x) = P([a]*x) <= P(x*x))
      

Admitted.

Hint Resolve Theorem179 : set.


(* 定理180 如果x和y都是C的元，而其中的不属于w，则P[x×y]=max[P[x],P[y]] *)

Theorem Theorem180 : forall x y,
  x ∈ C -> y ∈ C -> x ∉ W \/ y ∉ W -> P[x × y] = Max P[x] P[y].
Proof.
  intros; destruct H1.
  - assert (x ∈ (C ~ W)).
    { unfold Setminus; apply Theorem4'; split; auto.
      unfold Complement; apply AxiomII; split; Ens. }
    apply Theorem179 in H2.
    assert ((x × x) ≈ (x × y)).
    { unfold Equivalent.
  

Admitted.

Hint Resolve Theorem180 : set.


(* 定理181 存在唯一的≺-≺保序函数以R为定义域，并以C~w为值域  *)

Theorem Theorem181 : exists f, Order_Pr f E E /\ dom(f) = R /\ ran(f) = C ~ W.
Proof.
  intros.
  
  ~ Ensemble R
  
  x <> R -> Section x E R -> Ensemble x
  
  c1 <> C ~ W ->  Section c1 E (C~W) -> Ensemble c1
  { Section (c1 U W ) E R Theorem33}
  
  ~ Ensemble (C ~ W)
  { C ~ W U W = C }

Admitted.

Hint Resolve Theorem181 : set.

End A11.

Export A11.


