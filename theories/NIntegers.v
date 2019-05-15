Require Export Ordinals.

(* NON-NEGATIVE INTEGERS *)

Module NInt.

(* VIII Axiom of infinity : For some y, y is a set, Φ ∈ y and (x ∪ {x}) ∈ y
   whenever x ∈ y. *)

Axiom Axiom_Infinity : exists y, Ensemble y /\ Φ ∈ y /\
  (forall x, x ∈ y -> (x ∪ [x]) ∈ y).

Hint Resolve Axiom_Infinity : set.


(* 129 Definition  x is an integer if and only if x is an ordinal and E⁻¹
   well-orders x. *)

Definition NInteger x : Prop := Ordinal x /\ WellOrdered (E ⁻¹) x.

Hint Unfold NInteger : set.


(* 130 Definition  x is an E-last member of y is and only if x is an E⁻¹-first
   member of y. *)

Definition LastMember x E y : Prop := FirstMember x (E ⁻¹) y.

Hint Unfold LastMember : set.


(* 131 Definition  W = { x : x is an integer }. *)

Definition W : Class := \{ λ x, NInteger x \}.

Hint Unfold W : set.


(* 132 Theorem  A member of an integer is an integer. *)

Theorem Theorem132 : forall x y, NInteger x -> y∈x -> NInteger y.
Proof.
  intros.
  unfold NInteger in H; unfold NInteger; destruct H.
  double H; apply Lemma_xy with (y:= y∈x) in H2; auto.
  apply Theorem111 in H2; split; auto.
  unfold WellOrdered in H1; unfold WellOrdered.
  unfold Ordinal in H; destruct H.
  unfold full in H3; apply H3 in H0.
  destruct H1; split; intros.
  - unfold Connect in H1; unfold Connect; intros.
    apply H1; destruct H5; unfold Subclass in H0.
    apply H0 in H5; apply H0 in H6; split; auto.
  - destruct H5; apply H4; split; auto.
    apply (Theorem28 _ y _); auto.
Qed.

Hint Resolve Theorem132 : set.


(* 133 Theorem  If y∈R and x is an E-last member of y, then y = x+1. *)

Theorem Theorem133 : forall x y,
  y ∈ R /\ LastMember x E y -> y = PlusOne x.
Proof.
  intros; destruct H.
  unfold LastMember, FirstMember in H0.
  unfold R in H; apply Axiom_Scheme in H; destruct H, H0.
  double H1; add (x ∈ y) H3; apply Theorem111 in H3.
  assert (x ∈ R). { unfold R; apply Axiom_Scheme; Ens. }
  apply Theorem123 in H4; unfold FirstMember in H4; destruct H4.
  assert (y ∈ \{ λ z, z ∈ R /\ x ≺ z \}).
  { apply Axiom_Scheme; repeat split; auto.
    unfold R; apply Axiom_Scheme; split; auto. }
  apply H5 in H6; clear H5; generalize (Theorem113); intros.
  destruct H5; clear H7; apply Theorem107 in H5.
  unfold WellOrdered in H5; destruct H5; clear H7.
  unfold Connect in H5; apply Axiom_Scheme in H4; destruct H4, H7.
  clear H8; assert (y ∈ R /\ (PlusOne x) ∈ R).
  { split; auto; unfold R; apply Axiom_Scheme; Ens. }
  apply H5 in H8; clear H5; destruct H8; try contradiction.
  destruct H5; auto; unfold Rrelation, E in H5.
  apply Axiom_SchemeP in H5; destruct H5.
  apply H2 in H8; elim H8; unfold Rrelation, Inverse.
  apply Axiom_SchemeP; split; try apply Theorem49; Ens.
  unfold E; apply Axiom_SchemeP; split; try apply Theorem49; Ens.
  unfold PlusOne; apply Theorem4; right.
  unfold Singleton; apply Axiom_Scheme; Ens.
Qed.

Hint Resolve Theorem133 : set.


(* 134 Theorem  If x ∈ W, then x+1 ∈ W. *)

Theorem Theorem134 : forall x, x ∈ W -> (PlusOne x) ∈ W.
Proof.
  intros.
  unfold W in H; apply Axiom_Scheme in H; destruct H.
  unfold NInteger in H0; destruct H0.
  unfold W; apply Axiom_Scheme; split.
  - unfold PlusOne; apply Axiom_Union; split; auto.
    apply Theorem42 in H; auto.
  - unfold NInteger; split.
    + assert (x ∈ R). { apply Axiom_Scheme; Ens. }
      apply Lemma123 in H2; apply Axiom_Scheme in H2; apply H2.
    + unfold WellOrdered in H1; unfold WellOrdered.
      destruct H1; split; intros.
      { clear H2; unfold Connect in H1; unfold Connect; intros.
        unfold PlusOne in H2; destruct H2; apply Theorem4 in H2.
        apply Theorem4 in H3; destruct H2, H3.
        - apply H1; auto.
        - unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
          rewrite <- H4 in H2; try apply Theorem19; Ens.
          right; left; unfold Rrelation, Inverse, E.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply Axiom_Scheme in H2; destruct H2.
          rewrite <- H4 in H3; try apply Theorem19; Ens.
          left; unfold Rrelation, Inverse, E.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply Axiom_Scheme in H2; destruct H2.
          unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
          right; right; rewrite H4, H5; try apply Theorem19; Ens. }
      { destruct H3; unfold PlusOne in H3.
        generalize (classic (x ∈ y)); intro; destruct H5.
        - exists x; unfold FirstMember; split; intros; auto.
          intro; unfold Rrelation in H7; apply Axiom_SchemeP in H7.
          destruct H7; apply Axiom_SchemeP in H8; destruct H8.
          apply H3 in H6; apply Theorem4 in H6; destruct H6.
          + eapply Theorem102; eauto.
          + apply Axiom_Scheme in H6; destruct H6.
            rewrite H10 in H9; try apply Theorem19; Ens.
            apply Theorem101 in H9; auto.
        - apply H2; split; auto; unfold Subclass; intros; double H6.
          apply H3 in H6; apply Theorem4 in H6; destruct H6; auto.
          apply Axiom_Scheme in H6; destruct H6; apply Theorem19 in H.
          rewrite <- H8 in H5; auto; contradiction. }
Qed.

Hint Resolve Theorem134 : set.


(* 135 Theorem  Φ ∈ W and if x ∈ W, then Φ ≠ x+1. *)

Theorem Theorem135 : forall x, 
  Φ ∈ W /\ (x ∈ W -> Φ ≠ PlusOne x).
Proof.
  intros; split; intros.
  - unfold W; apply Axiom_Scheme; split.
    + generalize Axiom_Infinity; intros; destruct H, H, H0; Ens.
    + unfold NInteger; split.
      * unfold Ordinal; split.
        -- unfold Connect; intros; destruct H.
           generalize (Theorem16 u); contradiction.
        -- unfold full; intros.
           generalize (Theorem16 m); contradiction.
      * unfold WellOrdered; split; intros.
        -- unfold Connect; intros; destruct H.
           generalize (Theorem16 u); contradiction.
        -- destruct H; generalize (Theorem26 y); intros.
           absurd (y = Φ); try apply Theorem27; auto.
  - intro; unfold PlusOne in H0; assert (x ∈ Φ).
    { rewrite H0; apply Theorem4; right.
      unfold Singleton; apply Axiom_Scheme; split; Ens. }
    generalize (Theorem16 x); intro; contradiction.
Qed.

Hint Resolve Theorem135 : set.


(* 136 Theorem  If x and y are members of W and x + 1 = y + 1, then x = y. *)

Theorem Theorem136 : forall x y,
  x ∈ W /\ y ∈ W -> PlusOne x = PlusOne y -> x = y.
Proof.
  intros; destruct H.
  unfold W in H, H1; apply Axiom_Scheme in H.
  apply Axiom_Scheme in H1; destruct H, H1.
  unfold NInteger in H2, H3; destruct H2, H3.
  assert (x∈R /\ y∈R).
  { split; unfold R; apply Axiom_Scheme; auto. }
  destruct H6; apply Theorem124 in H6.
  apply Theorem124 in H7; rewrite <- H6, <- H7.
  rewrite H0; auto.
Qed.

Hint Resolve Theorem136 : set.


(* 137 Theorem  If x ⊂ W, Φ∈x and u+1∈x whenever u∈x, then x = W. *)

Corollary Property_W : Ordinal W.
Proof.
  unfold Ordinal; split.
  - unfold Connect; intros; destruct H; unfold W in H, H0.
    apply Axiom_Scheme in H; apply Axiom_Scheme in H0; destruct H, H0.
    unfold NInteger in H1, H2; destruct H1, H2; add (Ordinal v) H1.
    apply Theorem110 in H1; destruct H1 as [H1|[H1|H1]]; try tauto.
    + left; unfold Rrelation, E; apply Axiom_SchemeP.
      split; auto; apply Theorem49; split; auto.
    + right; left; unfold Rrelation, E; apply Axiom_SchemeP.
      split; auto; apply Theorem49; split; auto.
  - unfold full; intros; unfold Subclass; intros.
    unfold W in H; apply Axiom_Scheme in H; destruct H.
    apply (Theorem132 _ z) in H1; auto.
    unfold W; apply Axiom_Scheme; Ens.
Qed.

Theorem Theorem137 : forall x,
  x ⊂ W -> Φ ∈ x ->
  (forall u, u ∈ x -> (PlusOne u) ∈ x) -> x = W.
Proof.
  intros.
  generalize (classic (x = W)); intros; destruct H2; auto.
  assert (exists y, FirstMember y E (W ~ x)).
  { assert (WellOrdered E W).
    { apply Theorem107; apply Property_W. }
    unfold WellOrdered in H3; destruct H3; apply H4; split.
    - unfold Subclass; intros; unfold Difference in H5.
      apply Theorem4' in H5; apply H5.
    - intro; apply Property_Φ in H; apply H in H5.
      symmetry in H5; contradiction. }
  destruct H3 as [y H3]; unfold FirstMember in H3; destruct H3.
  unfold Difference in H3; apply Theorem4' in H3; destruct H3.
  unfold W in H3; apply Axiom_Scheme in H3; destruct H3; double H6.
  unfold NInteger in H7; destruct H7; unfold WellOrdered in H8.
  destruct H8; assert (y ⊂ y /\ y ≠ Φ).
  { split; try unfold Subclass; auto.
    intro; rewrite H10 in H5; unfold Complement in H5.
    apply Axiom_Scheme in H5; destruct H5; contradiction. }
  apply H9 in H10; clear H9; destruct H10 as [u H9].
  assert (u ∈ x).
  { unfold FirstMember in H9; destruct H9; clear H10.
    generalize (classic (u∈x)); intros; destruct H10; auto.
    assert (u ∈ (W ~ x)).
    { unfold Difference; apply Theorem4'; split.
      - unfold W; apply Axiom_Scheme; split; Ens.
        apply Theorem132 in H9; auto.
      - unfold Complement; apply Axiom_Scheme; Ens. }
    apply H4 in H11; elim H11; unfold Rrelation, E.
    apply Axiom_SchemeP; split; try apply Theorem49; Ens. }
  assert (y ∈ R /\ LastMember u E y).
  { split; auto; unfold R; apply Axiom_Scheme; Ens. }
  apply Theorem133 in H11; apply H1 in H10; rewrite <- H11 in H10.
  clear H11; unfold Complement in H5; apply Axiom_Scheme in H5.
  destruct H5; unfold NotIn in H11; contradiction.
Qed.

Hint Resolve Theorem137 : set.


(* 138 Theorem  W ∈ R. *)

Theorem Theorem138 : W ∈ R.
Proof.
  unfold R; apply Axiom_Scheme; split; try apply Property_W.
  generalize Axiom_Infinity; intros; destruct H, H, H0.
  assert (W ∩ x = W).
  { apply Theorem137; intros.
    - unfold Subclass; intros; apply Theorem4' in H2; apply H2.
    - apply Theorem4'; split; auto; apply Theorem135; auto.
    - apply Theorem4' in H2; destruct H2; apply Theorem134 in H2.
      apply H1 in H3; apply Theorem4'; split; auto. }
  rewrite <- H2; apply Theorem33 with (x:=x); auto.
  unfold Subclass; intros; apply Theorem4' in H3; apply H3.
Qed.

Hint Resolve Theorem138 : set.


(* Mathematical Induction *)

Theorem MiniMember_Principle : forall S,
  S ⊂ W /\ S ≠ Φ -> exists a, a ∈ S /\ (forall c, c ∈ S -> a ≼ c).
Proof.
  intros; destruct H.
  assert (exists y, FirstMember y E S).
  { assert (WellOrdered E W).
    { apply Theorem107; apply Property_W. }
    unfold WellOrdered in H1; destruct H1; apply H2; auto. }
  destruct H1; exists x; unfold FirstMember in H1; destruct H1.
  split; auto; intros; double H3; apply H2 in H4.
  unfold Subclass in H; apply H in H1; apply H in H3.
  unfold W in H1, H3; apply Axiom_Scheme in H1; apply Axiom_Scheme in H3.
  destruct H1, H3; unfold NInteger in H5, H6; destruct H5, H6.
  add (Ordinal c) H5; clear H6 H7 H8; apply Theorem110 in H5.
  unfold LessEqual; destruct H5 as [H5|[H5|H5]]; try tauto.
  elim H4; unfold Rrelation, E; apply Axiom_SchemeP; split; auto.
  apply Theorem49; split; Ens.
Qed.

Definition En_S P : Class := \{ λ x, x ∈ W /\ ~ (P x) \}.

Theorem Mathematical_Induction : forall (P: Class -> Prop),
  P Φ -> (forall k, k ∈ W /\ P k -> P (PlusOne k)) ->
  (forall n, n ∈ W -> P n).
Proof.
  intros.
  generalize (classic ((En_S P) = Φ)); intros; destruct H2.
  - generalize (classic (P n)); intros; destruct H3; auto.
    assert (n ∈ (En_S P)). { apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H4; generalize (Theorem16 n); contradiction.
  - assert ((En_S P) ⊂ W).
    { unfold En_S, Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    add ((En_S P) <> Φ) H3; clear H2.
    apply MiniMember_Principle in H3; destruct H3 as [h H3], H3.
    unfold En_S in H2; apply Axiom_Scheme in H2; destruct H2, H4.
    unfold W in H4; apply Axiom_Scheme in H4; clear H2; destruct H4.
    double H4; unfold NInteger in H6; destruct H6.
    unfold WellOrdered in H7; destruct H7.
    assert (h ⊂ h /\ h ≠ Φ).
    { split; try (unfold Subclass; intros; auto).
      generalize (classic (h = Φ)); intros; destruct H9; auto.
      rewrite H9 in H5; contradiction. }
    apply H8 in H9; clear H8; destruct H9.
    assert (h ∈ R /\ LastMember x E h).
    { split; auto; unfold R; apply Axiom_Scheme; split; auto. }
    apply Theorem133 in H9; unfold PlusOne in H9.
    unfold FirstMember in H8; destruct H8.
    generalize (classic (x ∈ (En_S P))); intros; destruct H11.
    + apply H3 in H11; assert (x ∈ h).
      { rewrite H9; apply Theorem4; right; apply Axiom_Scheme; Ens. }
      unfold LessEqual in H11; destruct H11.
      * add (x ∈ h) H11; clear H12.
        generalize (Theorem102 h x); intros; contradiction.
      * rewrite H11 in H12; generalize (Theorem101 x); contradiction.
    + assert (x ∈ (En_S P) <-> (Ensemble x /\ x ∈ W /\ ~ (P x))).
      { unfold En_S; split; intros.
        - apply Axiom_Scheme in H12; apply H12.
        - apply Axiom_Scheme; auto. }
      apply definition_not in H12; auto; clear H11.
      apply not_and_or in H12; destruct H12.
      * absurd (Ensemble x); Ens.
      * assert (x ∈ W).
        { unfold W; apply Axiom_Scheme; split; Ens.
          apply Theorem132 in H8; auto. }
        apply not_and_or in H11; destruct H11; try contradiction.
        apply NNPP in H11; add (P x) H12; clear H11.
        apply H0 in H12; unfold PlusOne in H12.
        rewrite <- H9 in H12; contradiction.
Qed.

Theorem The_Second_Mathematical_Induction : forall (P: Class -> Prop),
  P Φ -> (forall k, k ∈ W /\ (forall m, m ≺ k -> P m) -> P k) ->
  (forall n, n ∈ W -> P n).
Proof.
  intros.
  apply H0; split; auto; generalize dependent n.
  set (P' := (fun n => (forall j, j ∈ n -> P j))).
  generalize (Mathematical_Induction P'); intro.
  apply H1; red; intros.
  - destruct (Theorem16 j H2).
  - destruct H2; apply H0; split; intros.
    + apply Theorem134 in H2.
      unfold W in H2; apply Axiom_Scheme in H2; destruct H2.
      eapply Theorem132 in H5; eauto.
      unfold W; apply Axiom_Scheme; Ens.
    + apply H4; unfold PlusOne in H3.
      apply Axiom_Scheme in H3; destruct H3, H6.
      * unfold W in H2; apply Axiom_Scheme in H2; destruct H2.
        unfold NInteger in H7; destruct H7.
        unfold Ordinal in H7; destruct H7.
        unfold full in H9; eapply H9; eauto.
      * apply Axiom_Scheme in H6; destruct H6; AssE k.
        apply Theorem19 in H8; apply H7 in H8; subst j; auto.
Qed.

Theorem The_Second_Mathematical_Induction' : forall (P: Class -> Prop),
  P Φ -> (forall k, k ∈ W /\ (forall j, j ∈ k -> P j) -> P k) ->
  (forall n, n ∈ W -> P n).
Proof.
  intros.
  generalize (classic ((En_S P) = Φ)); intros; destruct H2.
  - generalize (classic (P n)); intros; destruct H3; auto.
    assert (n ∈ (En_S P)). { apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H4; generalize (Theorem16 n); contradiction.
  - assert ((En_S P) ⊂ W).
    { unfold En_S, Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    add ((En_S P) <> Φ) H3; clear H2.
    apply MiniMember_Principle in H3; destruct H3 as [h H3], H3.
    unfold En_S in H2; apply Axiom_Scheme in H2; destruct H2, H4.
    assert (forall a, a ∈ W -> a = Φ \/ exists b, a = (PlusOne b)).
    { apply Mathematical_Induction; auto; intros; right; eauto. }
    destruct H6 with h; auto.
    + rewrite H7 in H5; contradiction.
    + destruct H7; subst h.
      elim H5; apply H0; split; auto; intros.
      generalize (classic (P j)); intros; destruct H8; auto.
      assert (j ∈ (En_S P)).
      { apply Axiom_Scheme; repeat split; Ens.
        unfold W in H4; apply Axiom_Scheme in H4; clear H2; destruct H4.
        apply Axiom_Scheme; split; Ens; eapply Theorem132; eauto. }
      apply H3 in H9; destruct H9.
      * add ((PlusOne x) ∈ j) H7; clear H9.
        destruct (Theorem102 _ _ H7).
      * subst j; destruct (Theorem101 _ H7).
Qed.

Theorem Mathematical_Induction_Theorem137 : forall (P: Class -> Prop),
  (P Φ -> (forall k, k ∈ W /\ P k -> P (PlusOne k)) ->
  (forall n, n ∈ W -> P n)) <->
  (\{ λ x, x ∈ W /\ P x \} ⊂ W -> Φ ∈ \{ λ x, x ∈ W /\ P x \} -> (forall u,
  u ∈ \{ λ x, x ∈ W /\ P x \} -> (PlusOne u) ∈ \{ λ x, x ∈ W /\ P x \}) ->
  \{ λ x, x ∈ W /\ P x \} = W).
Proof.
  split; intros.
  - apply Axiom_Scheme in H1; destruct H1, H3; apply Axiom_Extent; split; intros.
    + apply H0 in H5; auto.
    + apply H with (n:= z) in H4; auto; try apply Axiom_Scheme; Ens; intros.
      destruct H6; assert (k ∈ \{λ x, x∈W /\ P x\}). { apply Axiom_Scheme; Ens. }
      apply H2 in H8; apply Axiom_Scheme in H8; apply H8.
  - assert (\{ λ x, x ∈ W /\ P x \} ⊂ W).
    { unfold Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    assert (Φ ∈ \{ λ x, x ∈ W /\ P x \}).
    { apply Axiom_Scheme; generalize (Theorem135 n); intros.
      destruct H4 as [H4 _]; Ens. }
    assert ((forall u, u ∈ \{ λ x, x ∈ W /\ P x \} ->
     (PlusOne u) ∈ \{ λ x, x ∈ W /\ P x \})).
    { intros; apply Axiom_Scheme in H5; destruct H5, H6; double H6.
      apply Theorem134 in H8; apply Axiom_Scheme; repeat split; Ens. }
    apply H in H5; auto; rewrite <- H5 in H2; clear H H3 H4 H5.
    apply Axiom_Scheme in H2; apply H2.
Qed.

End NInt.

Export NInt.

