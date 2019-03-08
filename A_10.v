Require Export A_9.

(* A.10 选择公理 *)

Module A10.

(* 定义139 *)

Definition ChoiceFunction c : Prop :=
  Function c /\ (forall x, x ∈ dom(c) -> c[x] ∈ x).

Hint Unfold ChoiceFunction : set.


(* 选择公理 IX *)

Axiom AxiomIX : exists c, ChoiceFunction c /\ dom(c) = μ ~ [Φ].

Hint Resolve AxiomIX : set.


(* 定理140 *)

Lemma Ex_Lemma140 : forall x c,
  Ensemble x -> ChoiceFunction c ->
  (exists g, forall h, Ensemble h -> g[h] = c[x ~ ran(h)]).
Proof.
  intros.
  unfold ChoiceFunction in H0; destruct H0.
  exists (\{\ λ u v, v = c [x ~ ran(u)] \}\); intros.
  apply AxiomI; split; intros.
  - apply AxiomII; split; Ens; intros.
    apply AxiomII in H3; destruct H3.
    apply H5; clear H5; apply AxiomII; split; Ens.
    apply AxiomII_P; split; try apply Theorem49; Ens.
    apply AxiomII in H4; destruct H4.
    rewrite Theorem70 in H5; auto.
    apply AxiomII_P in H5; apply H5.
  - apply AxiomII; split; Ens; intros.
    apply AxiomII in H4; destruct H4.
    apply AxiomII_P in H5; destruct H5.
    rewrite H6; auto.
Qed.

(** Lemma96 **)

Lemma Property_F11 : forall f,
  dom(f⁻¹) = ran(f) /\ ran(f⁻¹) = dom(f).
Proof.
  intros; rewrite <- Lemma96, <- Lemma96'; auto.
Qed.

Lemma Lemma140 : forall f g y,
  y ∈ dom(f) -> f [y] = g [f | y] -> Ensemble (f | y).
Proof.
  intros.
  generalize (classic ((f|y) ∈ dom(g))); intros; destruct H1; Ens.
  apply Theorem69 in H1; rewrite H1 in H0; clear H1.
  apply Theorem69 in H; rewrite H0 in *.
  generalize (Theorem101 μ); intros; contradiction.
Qed.

Theorem Theorem140 : forall x,
  Ensemble x -> exists f, Function1_1 f /\ ran(f) = x /\ Ordinal_Number dom(f).
Proof.
  intros.
  generalize AxiomIX; intros; destruct H0 as [c H0], H0.
  double H0; apply (Ex_Lemma140 x _) in H2; auto; destruct H2 as [g H2].
  generalize (Theorem128 g); intros; destruct H3 as [f H3], H3, H4.
  unfold ChoiceFunction in H0; destruct H0; exists f.
  assert (Function1_1 f).
  { unfold Function1_1; split; auto.
    unfold Function; split; intros.
    - unfold Relation; intros; PP H7 a b; Ens.
    - unfold Inverse in H7; destruct H7.
      apply AxiomII_P in H7; apply AxiomII_P in H8; destruct H7, H8.
      clear H7 H8; double H9; apply Property_dom in H8.
      double H10; apply Property_dom in H10.
      generalize (classic (y = z)); intros; destruct H11; auto.
      assert (Ordinal y /\ Ordinal z).
      { split; apply (Theorem111 dom(f) _); auto. }
      elim H12; intros; apply Theorem110 in H12.
      assert (Ordinal_Number y /\ Ordinal_Number z).
      { unfold Ordinal_Number, R; split; apply AxiomII; Ens. }
      clear H13 H14; destruct H15; apply H5 in H13; apply H5 in H14.
      rewrite H2 in H13, H14; try apply (Lemma140 _ g _); auto.
      clear H2 H5; apply Property_Value in H8; auto.
      apply Property_Value in H10; auto.
      unfold Function in H3; destruct H3.
      add ([y,f[y]] ∈ f) H7; add ([z,f[z]] ∈ f) H9.
      apply H3 in H7; apply H3 in H9; rewrite H9 in H7; clear H9.
      double H8; double H10; apply Property_ran in H8.
      apply Property_ran in H10; destruct H12.
      + assert (f[z] ∈ ran(f|z)).
        { rewrite H7; unfold Range; apply AxiomII; split; Ens.
          exists y; unfold Restriction; apply Theorem4'; split; auto.
          unfold Cartesian; apply AxiomII_P; split; Ens.
          split; auto; apply Theorem19; Ens. }
        assert ((x ~ ran(f|z)) ∈ dom(c)).
        { generalize (classic ((x ~ ran(f|z)) ∈ dom(c))); intros.
          destruct H16; auto; apply Theorem69 in H16; auto.
          rewrite H16 in H14; rewrite H14 in H10; AssE μ.
          generalize Theorem39; intros; contradiction. }
        apply H6 in H16; unfold Setminus at 2 in H16.
        rewrite <- H14 in H16; apply Theorem4' in H16; destruct H16.
        unfold Complement in H17; apply AxiomII in H17; destruct H17.
        unfold NotIn in H18; contradiction.
      + destruct H12; try contradiction.
        assert (f[y] ∈ ran(f|y)).
        { rewrite <- H7; unfold Range; apply AxiomII; split; Ens.
          exists z; unfold Restriction; apply Theorem4'; split; auto.
          unfold Cartesian; apply AxiomII_P; split; Ens.
          split; auto; apply Theorem19; Ens. }
        assert ((x ~ ran(f|y)) ∈ dom(c)).
        { generalize (classic ((x ~ ran(f|y)) ∈ dom(c))); intros.
          destruct H16; auto; apply Theorem69 in H16; auto.
          rewrite H16 in H13; rewrite H13 in H8; AssE μ.
          generalize Theorem39; intros; contradiction. }
        apply H6 in H16; unfold Setminus at 2 in H16.
        rewrite <- H13 in H16; apply Theorem4' in H16; destruct H16.
        unfold Complement in H17; apply AxiomII in H17; destruct H17.
        unfold NotIn in H18; contradiction. }
  split; auto; assert (ran(f) ⊂ x).
  { unfold Included; intros; unfold Range in H8; apply AxiomII in H8.
    destruct H8, H9; double H9; apply Property_dom in H10.
    assert (Ordinal_Number x0).
    { unfold Ordinal_Number, R; apply AxiomII; split; Ens.
      apply (Theorem111 dom(f) _); split; auto. }
    apply H5 in H11; rewrite H2 in H11; try apply (Lemma140 _ g _); auto.
    apply Property_Value in H10; auto; destruct H3.
    add ([x0,f[x0]]∈f) H9; apply H12 in H9; rewrite <- H9 in H11.
    assert ((x ~ ran(f|x0)) ∈ dom(c)).
    { generalize (classic ((x ~ ran(f|x0)) ∈ dom(c))); intros.
      destruct H13; auto; apply Theorem69 in H13; auto.
      rewrite H13 in H11; rewrite H11 in H9; rewrite <- H9 in H10.
      clear H9 H11 H13; apply Property_ran in H10; AssE μ.
      generalize Theorem39; intros; contradiction. }
    apply H6 in H13; rewrite <- H11 in H13.
    unfold Setminus in H13; apply Theorem4' in H13; apply H13. }
  assert (Ensemble dom(f)).
  { unfold Function1_1 in H7; destruct H7 as [H9 H7]; clear H9.
    generalize (Property_F11 f); intros; destruct H9; rewrite <- H9 in H8.
    rewrite <- H10; apply AxiomV; apply Theorem33 in H8; auto. }
  assert (Ordinal_Number dom(f)).
  { unfold Ordinal_Number; apply AxiomII; split; auto. }
  split; auto; apply H5 in H10.
  assert (f|dom(f) = f).
  { unfold Restriction; apply AxiomI; split; intros.
    - apply AxiomII in H11; apply H11.
    - apply AxiomII; repeat split; Ens.
      PP' H12 a b; apply AxiomII_P; repeat split; Ens.
      + apply Property_dom in H11; auto.
      + apply Property_ran in H11; apply Theorem19; Ens. }
  rewrite H11 in *; clear H11.
  rewrite H2 in H10; try apply Theorem75; auto.
  generalize (Theorem101 dom(f)); intros.
  apply Theorem69 in H11; auto; rewrite H10 in H11.
  generalize (classic ((x ~ ran(f)) ∈ dom(c))); intros; destruct H12.
  - apply Theorem69 in H12; auto; rewrite H11 in H12.
    generalize (Theorem101 μ); intros; contradiction.
  - rewrite H1 in H12; unfold Setminus at 2 in H12.
    assert ((x ~ ran(f)) ∈ (μ ∩ ¬[Φ]) <-> (x ~ ran(f)) ∈ μ /\
            (x ~ ran(f)) ∈ ¬[Φ]).
    { split; intros; try apply Theorem4'; auto. }
    apply definition_not in H13; auto; clear H12.
    assert (Ensemble (x ~ ran(f))).
    { apply (Theorem33 x _); auto; unfold Included.
      intros; apply AxiomII in H12; apply H12. }
    apply not_and_or in H13; destruct H13.
    + elim H13; apply Theorem19; auto.
    + assert ((x ~ ran(f)) ∈ ¬[Φ] <-> Ensemble (x ~ ran(f)) /\
              (x ~ ran(f)) ∉ [Φ]).
      { split; intros; try apply AxiomII; auto.
        apply AxiomII in H14; apply H14. }
      apply definition_not in H14; auto; clear H13.
      apply not_and_or in H14; destruct H14; try contradiction.
      unfold NotIn in H13; apply NNPP in H13.
      unfold Singleton in H13; apply AxiomII in H13; destruct H13.
      generalize AxiomVIII; intros; destruct H15, H15, H16.
      AssE Φ; clear H15 H16 H17; apply Theorem19 in H18.
      apply H14 in H18; symmetry; apply -> Property_Φ in H18; auto.
Qed.

Hint Resolve Theorem140 : set.


(* 定义141 *)

Definition Nest n : Prop :=
  forall x y, x ∈ n /\ y ∈ n -> x ⊂ y \/ y ⊂ x.

Hint Unfold Nest : set.


(* 定理142 *)

Theorem Theorem142 : forall n,
  Nest n /\ (forall m, m ∈ n -> Nest m) -> Nest (∪ n).
Proof.
  intros; destruct H.
  unfold Nest; intros; destruct H1.
  unfold Element_U in H1, H2; apply AxiomII in H1.
  apply AxiomII in H2; destruct H1, H2, H3, H4, H3, H4.
  unfold Nest in H; assert (x0∈n /\ x1∈n). { Ens. }
  apply H0 in H5; apply H0 in H6; apply H in H7; destruct H7.
  - unfold Included in H7; apply H7 in H3; clear H7.
    unfold Nest in H6; apply H6; auto.
  - unfold Included in H7; apply H7 in H4; clear H7.
    unfold Nest in H5; apply H5; auto.
Qed.

Hint Resolve Theorem142 : set.


(* 定理143 *)

Definition En_c x h : Class :=
  \{ λ m, Nest m /\ m ⊂ x /\ (forall p, p ∈ ran(h) -> p ⊂ m /\ p <> m) \}.

Lemma Ex_Lemma143 : forall x c,
  Ensemble x -> ChoiceFunction c ->
  (exists g, forall h, Ensemble h -> g[h] = c[En_c x h]).
Proof.
  intros.
  unfold ChoiceFunction in H0; destruct H0.
  exists (\{\ λ u v, v = c[En_c x u] \}\); intros.
  apply AxiomI; split; intros.
  - apply AxiomII; split; Ens; intros.
    apply AxiomII in H3; destruct H3.
    apply H5; clear H5; apply AxiomII; split; Ens.
    apply AxiomII_P; split; try apply Theorem49; Ens.
    apply AxiomII in H4; destruct H4.
    rewrite Theorem70 in H5; auto.
    apply AxiomII_P in H5; apply H5.
  - apply AxiomII; split; Ens; intros.
    apply AxiomII in H4; destruct H4.
    apply AxiomII_P in H5; destruct H5.
    rewrite H6; auto.
Qed.

Lemma Lemma143 : forall f z,
  Function f -> z ∈ (∪ ran(f)) -> exists x, z ∈ f [x] /\ x ∈ dom(f).
Proof.
  intros.
  unfold Element_U in H0; apply AxiomII in H0.
  destruct H0, H1 as [y H1], H1; unfold Range in H2.
  apply AxiomII in H2; destruct H2, H3 as [x H3].
  double H3; rewrite Theorem70 in H4; auto.
  apply AxiomII_P in H4; destruct H4; rewrite H5 in *.
  apply Property_dom in H3; Ens.
Qed.

Theorem Theorem143 : forall x,
  Ensemble x -> exists n, (Nest n /\ n ⊂ x) /\
  (forall m, Nest m -> m ⊂ x /\ n ⊂ m -> m = n).
Proof.
  intros.
  generalize AxiomIX; intros; destruct H0 as [c H0], H0.
  double H0; apply (Ex_Lemma143 x _) in H2; auto; destruct H2 as [g H2].
  generalize (Theorem128 g); intros; destruct H3 as [f H3], H3, H4.
  unfold ChoiceFunction in H0; destruct H0.
  (* 如果 u ∈ dom(f)，则 f[u] 是 x 中的一个套。 *)
  assert (forall u, u ∈ dom(f) -> Nest f[u] /\ f[u] ⊂ x /\
         (forall p, p ∈ ran(f|u) -> p ⊊ f[u])).
  { intros; assert (Ordinal_Number u).
    { unfold Ordinal_Number, R; apply AxiomII.
      split; try apply (Theorem111 dom(f) _); Ens. }
    apply H5 in H8; rewrite H2 in H8; try apply (Lemma140 _ g _); auto.
    assert (En_c x (f|u) ∈ dom(c)).
    { generalize (classic (En_c x (f|u) ∈ dom(c))); intros.
      destruct H9; auto; apply Theorem69 in H9; auto.
      rewrite H9 in H8; clear H9; apply Property_Value in H7; auto.
      apply Property_ran in H7; rewrite H8 in H7; AssE μ.
      generalize Theorem39; intros; contradiction. }
    apply H6 in H9; rewrite <- H8 in H9; clear H8.
    apply AxiomII in H9; apply H9. }
  (* 如果 u 与 v 均为 dom(f) 的元，并且 u<v，则 f[u] ⊊ f[v]。 *)
  assert (forall u v, u ∈ dom(f) -> v ∈ dom(f) -> u ∈ v -> f[u] ⊊ f[v]).
  { intros; apply H7 in H9; clear H7; destruct H9, H9.
    apply H11; unfold Range; apply AxiomII.
    apply Property_Value in H8; auto; double H8.
    apply Property_ran in H12; split; Ens; exists u.
    unfold Restriction; apply Theorem4'; split; auto.
    unfold Cartesian; apply AxiomII_P; split; Ens.
    split; try apply Theorem19; Ens. }
  exists (∪ ran(f)); intros; split; intros; try split.
  - unfold Nest; intros z0 z1 H9; destruct H9.
    apply Lemma143 in H9; apply Lemma143 in H10; auto.
    destruct H9, H10, H9, H10.
    assert (Ordinal x0 /\ Ordinal x1).
    { split; apply (Theorem111 dom(f) _); auto. }
    apply Theorem110 in H13; destruct H13 as [H13|[H13|H13]].
    + apply H8 in H13; auto; unfold ProperSubset in H13.
      destruct H13; apply H13 in H9; clear H13 H14.
      apply H7 in H12; destruct H12; clear H13.
      unfold Nest in H12; apply H12; auto.
    + apply H8 in H13; auto; unfold ProperSubset in H13.
      destruct H13; apply H13 in H10; clear H13 H14.
      apply H7 in H11; destruct H11; clear H13.
      unfold Nest in H11; apply H11; auto.
    + rewrite H13 in H9; apply H7 in H12; destruct H12.
      unfold Nest in H12; apply H12; auto.
  - unfold Included; intros; apply Lemma143 in H9; auto.
    destruct H9, H9; apply H7 in H10; destruct H10, H11.
    unfold Included in H11; apply H11; auto.
  - destruct H10; generalize (Theorem101 dom(f)); intros.
    apply Theorem69 in H12.
    assert (Function f⁻¹).
    { unfold Function; split; intros.
      - unfold Relation; intros; PP H13 a b; Ens.
      - destruct H13; unfold Inverse in H13, H14.
        apply AxiomII_P in H13; apply AxiomII_P in H14.
        destruct H13, H14; double H15; double H16.
        rewrite Theorem70 in H17, H18; auto.
        apply AxiomII_P in H17; apply AxiomII_P in H18.
        destruct H17, H18; rewrite H19 in H20.
        clear H17 H18 H19; apply Property_dom in H15.
        apply Property_dom in H16.
        assert (Ordinal y /\ Ordinal z).
        { split; apply (Theorem111 dom(f) _); auto. }
        apply Theorem110 in H17; destruct H17.
        + apply H8 in H17; auto; unfold ProperSubset in H17.
          destruct H17; contradiction.
        + destruct H17; auto; apply H8 in H17; auto.
          destruct H17; symmetry in H20; contradiction. }
    assert (Ensemble dom(f)).
    { generalize (Property_F11 f); intros; destruct H14.
      rewrite <- H15; apply AxiomV; auto; rewrite H14.
      apply (Theorem33 pow(x) _); try (apply Theorem38 in H; auto).
      unfold Included; intros; unfold Range in H16; apply AxiomII in H16.
      destruct H16, H17; double H17; rewrite Theorem70 in H18; auto.
      apply AxiomII_P in H18; destruct H18; rewrite H19 in *; clear H18 H19.
      apply Property_dom in H17; apply H7 in H17; destruct H17, H18.
      unfold PowerSet; apply AxiomII; split; auto. }
    assert (Ordinal_Number dom(f)).
    { unfold Ordinal_Number, R; apply AxiomII; split; auto. }
    apply H5 in H15; assert (f|dom(f) = f).
    { unfold Restriction; apply AxiomI; split; intros.
      - apply AxiomII in H16; apply H16.
      - apply AxiomII; repeat split; Ens.
        PP' H17 a b; apply AxiomII_P; repeat split; Ens.
        + apply Property_dom in H16; auto.
        + apply Property_ran in H16; apply Theorem19; Ens. }
    rewrite H16 in *; rewrite H15 in H12; clear H15 H16.
    rewrite H2 in H12; try apply Theorem75; auto.
    generalize (classic (En_c x f ∈ dom(c))); intros; destruct H15.
    + apply Theorem69 in H15; auto; rewrite H12 in H15.
      generalize (Theorem101 μ); intros; contradiction.
    + rewrite H1 in H15; unfold Setminus in H15.
      assert (En_c x f ∈ (μ ∩ ¬[Φ]) <-> En_c x f ∈ μ /\ En_c x f ∈ ¬[Φ]).
      { split; intros; try apply Theorem4'; auto. }
      apply definition_not in H16; auto; clear H15.
      assert (Ensemble (En_c x f)).
      { apply (Theorem33 pow(x) _); try (apply Theorem38 in H; auto).
        unfold Included; intros; unfold En_c in H15.
        apply AxiomII in H15; destruct H15, H17, H18.
        unfold PowerSet; apply AxiomII; split; auto. }
      apply not_and_or in H16; destruct H16.
      * elim H16; apply Theorem19; auto.
      * assert (En_c x f ∈ ¬[Φ] <-> Ensemble (En_c x f) /\ En_c x f ∉ [Φ]).
        { split; intros; try apply AxiomII; auto.
          apply AxiomII in H17; apply H17. }
        apply definition_not in H17; auto; clear H16.
        apply not_and_or in H17; destruct H17; try contradiction.
        unfold NotIn in H16; apply NNPP in H16.
        unfold Singleton in H16; apply AxiomII in H16; destruct H16.
        generalize AxiomVIII; intros; destruct H18, H18, H19.
        AssE Φ; clear H18 H19 H20; apply Theorem19 in H21.
        apply H17 in H21; clear H17.
        generalize (classic (m = ∪ ran( f))); intros; destruct H17; auto.
        assert (m ∈ (En_c x f)).
        { unfold En_c; apply AxiomII; repeat split; auto.
          - apply (Theorem33 x _); auto.
          - unfold Included; intros; apply H11.
            unfold Element_U; apply AxiomII; split; Ens.
          - intro; rewrite H19 in H18; clear H19.
            elim H17; apply Theorem27; split; auto.
            unfold Included; intros; apply AxiomII; Ens. }
        rewrite H21 in H18; generalize (Theorem16 m); contradiction.
Qed.

Hint Resolve Theorem143 : set.

End A10.

Export A10.


