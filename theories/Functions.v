Require Export Ordered_Pairs.

(* FUNCTIONS *)

Module Fun.

(* 63 Definition  f is a function if and only if f is a relation and for each x,
   each y, each z, if [x,y]∈f and [x,z]∈f, then y = z. *)

Definition Function f : Prop :=
  Relation f /\ (forall x y z, [x,y] ∈ f /\ [x,z] ∈ f -> y=z).

Hint Unfold Function : set.


(* 64 Theorem  If f is a function and g is a function so is f∘g. *)

Theorem Theorem64 : forall f g,
  Function f /\ Function g -> Function (f ∘ g).
Proof.
  intros; destruct H.
  unfold Function; split; intros.
  - unfold Relation; intros; PP H1 a b; eauto.
  - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1, H2, H3, H4, H3, H4.
    unfold Function in H, H0; destruct H; destruct H0.
    assert (x0=x1). { apply H8 with x; split; auto. }
    rewrite H9 in H5; apply H7 with x1; split; auto.
Qed.

Hint Resolve Theorem64 : set.


(* 65 Definition  domain f = { x : for some y, [x,y]∈f }. *)

Definition Domain f : Class := \{ λ x, exists y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

Corollary Property_dom : forall x y f,
  [x,y] ∈ f -> x ∈ dom( f ).
Proof.
  intros; unfold Domain; apply Axiom_Scheme; split; eauto.
  AssE [x,y]; apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Domain : set.


(* 66 Definition  range f = { y : for some x, [x,y]∈f }. *)

Definition Range f : Class := \{ λ y, exists x, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

Corollary Property_ran : forall x y f,
  [x,y] ∈ f -> y ∈ ran( f ).
Proof.
  intros; apply Axiom_Scheme.
  split; eauto; AssE [x,y].
  apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Range : set.


(* 67 Theorem  domain μ = μ and range μ = μ. *)

Theorem Theorem67 : dom( μ ) = μ /\ ran( μ ) = μ.
Proof.
  intros; split; apply Axiom_Extent; split; intros.
  - AssE z; apply Theorem19; auto.
  - apply Theorem19 in H.
    unfold Domain; apply Axiom_Scheme; split; auto.
    exists z; apply Theorem19.
    apply Theorem49; split; auto.
  - AssE z; apply Theorem19; auto.
  - apply Theorem19 in H.
    unfold Range; apply Axiom_Scheme; split; auto.
    exists z; apply Theorem19.
    apply Theorem49; split; auto.
Qed.

Hint Rewrite Theorem67 : set.


(* 68 Definition  f[x] = ∩{ y : [x,y]∈f }. *)

Definition Value f x : Class := ∩ \{ λ y, [x,y] ∈ f \}.

Notation "f [ x ]" := (Value f x)(at level 5).

Corollary Property_Value : forall f x,
  Function f -> x ∈ dom( f ) -> [x,f[x]] ∈ f.
Proof.
  intros; unfold Function in H;destruct H as [_ H].
  apply Axiom_Scheme in H0; destruct H0, H1.
  assert (x0=f[x]).
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme; split; intros; try Ens.
      apply Axiom_Scheme in H3; destruct H3.
      assert (x0=y). { apply H with x; split; auto. }
      rewrite <- H5; auto.
    + apply Axiom_Scheme in H2; destruct H2 as [_ H2].
      apply H2; apply Axiom_Scheme; split; auto.
      AssE [x, x0]; apply Theorem49 in H3; apply H3.
  - rewrite <- H2; auto.
Qed.

Hint Unfold Value : set.
Hint Resolve Property_Value : set.


(* 69 Theorem  If x ∉ domain f, then f[x]=μ; if x ∈ domain f, then f[x]∈μ. *)

Lemma Lemma69 : forall x f,
  Function f -> (x ∉ dom(f) -> \{ λ y, [x,y] ∈ f \} = Φ) /\
  (x ∈ dom(f) -> \{ λ y, [x,y] ∈ f \} <> Φ).
Proof.
  intros; split; intros.
  - generalize (classic (\{ λ y0, [x, y0] ∈ f \} = Φ)); intro.
    destruct H1; auto; apply Lemma35 in H1; auto.
    elim H1; intro z; intros; apply Axiom_Scheme in H2.
    destruct H2 as [H2 H3]; apply Property_dom in H3; contradiction.
  - apply Lemma35; auto; exists f[x].
    apply Axiom_Scheme; eapply Property_Value in H0; auto.
    split; auto; apply Property_ran in H0; Ens.
Qed.

Theorem Theorem69 : forall x f,
  ( x ∉ dom( f ) -> f[x] = μ ) /\ ( x ∈ dom( f ) -> f[x] ∈  μ ).
Proof.
  intros; split; intros.
  - assert (\{ λ y, [x,y] ∈ f \} = Φ).
    { apply Axiom_Extent; split; intros.
      apply Axiom_Scheme in H0; destruct H0.
      apply Property_dom in H1; contradiction.
      generalize (Theorem16 z); intro; contradiction. }
    unfold Value; rewrite H0; apply Theorem24.
  - assert (\{ λ y, [x,y] ∈ f \} <> Φ).
    { intro; apply Axiom_Scheme in H; destruct H, H1.
      generalize (Axiom_Extent \{ λ y, [x, y] ∈ f \} Φ); intro.
      destruct H2; apply H2 with x0 in H0; destruct H0.
      assert (x0 ∈ Φ).
      { apply H0; apply Axiom_Scheme; split; auto.
        AssE [x, x0];  apply Theorem49 in H5; tauto. }
      eapply Theorem16; eauto. }
    apply Theorem35 in H0; apply Theorem19; auto.
Qed.

Corollary Property_Value' : forall f x,
  Function f -> f[x] ∈ ran(f) -> [x,f[x]] ∈ f.
Proof.
  intros; apply Property_Value; auto.
  apply Axiom_Scheme in H0; destruct H0, H1.
  generalize (classic (x ∈ dom( f))); intros.
  destruct H2; auto; apply Theorem69 in H2; auto.
  rewrite H2 in H0; generalize (Theorem39); intro; contradiction.
Qed.

Hint Resolve Theorem69 : set.
Hint Resolve Property_Value' : set.


(* 70 Theorem  If f is a function, then f = { [x,y] : y = f[x] }. *)

Theorem Theorem70 : forall f,
  Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - double H0; unfold Function, Relation in H; destruct H.
    apply H in H1; destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply Axiom_SchemeP; split; try Ens; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme; split; intros; try Ens.
      apply Axiom_Scheme in H3; destruct H3.
      apply Lemma_xy with (y:=[a, y] ∈ f) in H0; auto.
      apply H2 in H0; rewrite <- H0; auto.
    + unfold Value, Element_I in H1; apply Axiom_Scheme in H1; destruct H1.
      apply H3; apply Axiom_Scheme; split; auto; AssE [a,b].
      apply Theorem49 in H4; try apply H4.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
    generalize (classic (a ∈ dom( f ))); intros; destruct H3.
    + apply Property_Value in H3; auto; rewrite H2; auto.
    + apply Theorem69 in H3; auto.
      rewrite H3 in H2; rewrite H2 in H1.
      apply Theorem49 in H1; destruct H1 as [_ H1].
      generalize Theorem39; intro; contradiction.
Qed.

Hint Resolve Theorem70 : set.


(* 71 Theorem  If f and g are functions, then f=g iff f[x]=g[x] for each x. *)

Theorem Theorem71 : forall f g,
  Function f /\ Function g -> (f = g <-> forall x, f[x] = g[x]).
Proof.
  intros; split; intros; try rewrite H0; trivial.
  destruct H; intros; apply (Theorem70 f) in H; apply (Theorem70 g) in H1.
  rewrite H; rewrite H1; apply Axiom_Extent; split; intros.
  - PP H2 a b; apply Axiom_SchemeP in H3; apply Axiom_SchemeP.
    destruct H3; split; auto; rewrite <- H0; auto.
  - PP H2 a b; apply Axiom_SchemeP in H3; apply Axiom_SchemeP.
    destruct H3; split; auto; rewrite -> H0; auto.
Qed.

Hint Resolve Theorem71 : set.


(* V Axiom of substitution  If f is a function and domain f is a set, then 
   range f is a set. *)

Axiom Axiom_Substitution : forall f,
  Function f -> Ensemble dom(f) -> Ensemble ran(f).

Hint Resolve Axiom_Substitution : set.


(* VI Axiom of amalgamation  If x is a set so is ∪x. *)

Axiom Axiom_Amalgamation : forall x, Ensemble x -> Ensemble (∪ x).

Hint Resolve Axiom_Amalgamation : set.


(* 72 Definition  x × y = { [u,v] : u∈x /\ v∈y }. *)

Definition Cartesian x y : Class := \{\ λ u v, u∈x /\ v∈y \}\.

Notation "x × y" := (Cartesian x y)(at level 2, right associativity).

Hint Unfold Cartesian : set.


(* 73 Theorem  If u and y are sets so is [u] × y. *)

Lemma Ex_Lemma73 : forall u y,
  Ensemble u /\ Ensemble y ->
  exists f, Function f /\ dom(f) = y /\ ran(f) = [u] × y.
Proof.
  intros; destruct H.
  exists (\{\ λ w z, w∈y /\ z = [u,w] \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; Ens.
  - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1 as [_ [_ H1]]; destruct H2 as [_ [_ H2]].
    rewrite H2; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1 as [_ [t H1]].
      apply Axiom_SchemeP in H1; tauto.
    + apply Axiom_Scheme; split; try Ens.
      exists [u,z]; apply Axiom_SchemeP; split; auto.
      AssE z; apply Theorem49; split; auto.
      apply Theorem49; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H1, H2.
      apply Axiom_SchemeP in H2; destruct H2, H3.
      rewrite H4; apply Axiom_SchemeP; repeat split; auto.
      * apply Theorem49; split; auto; AssE x0.
      * apply Axiom_Scheme; split; auto.
    + PP H1 a b; apply Axiom_SchemeP in H2; destruct H2, H3.
      apply Axiom_Scheme; split; auto; exists b.
      apply Axiom_SchemeP; repeat split; auto.
      * apply Theorem49; split; auto; AssE b.
      * apply Theorem19 in H; apply Axiom_Scheme in H3.
        destruct H3; rewrite H5; auto.
Qed.

Theorem Theorem73 : forall u y,
  Ensemble u /\ Ensemble y -> Ensemble ([u] × y).
Proof.
  intros.
  elim H; intros; apply Ex_Lemma73 in H; auto.
  destruct H, H, H2; rewrite <- H3; apply Axiom_Substitution; auto.
  rewrite H2; auto.
Qed.

Hint Resolve Theorem73 : set.


(* 74 Theorem  If x and y are sets so is x × y. *)

Lemma Ex_Lemma74 : forall x y,
  Ensemble x /\ Ensemble y -> exists f, Function f /\ dom( f ) = x /\
  ran( f ) = \{ λ z, exists u, u∈x /\ z = [u] × y \}.
Proof.
  intros; destruct H.
  exists (\{\ λ u z, u∈x /\ z = [u] × y \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; Ens.
  - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1, H2, H3, H4; subst z; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; tauto.
    + apply Axiom_Scheme; split; try AssE z.
      exists (([z]) × y); apply Axiom_SchemeP.
      repeat split; auto; apply Theorem49; split; auto.
      apply Theorem73; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; apply Axiom_Scheme.
      split; auto; exists x0; tauto.
    + apply Axiom_Scheme in H1; destruct H1, H2, H2.
      apply Axiom_Scheme; split; auto.
      exists x0; apply Axiom_SchemeP; repeat split; auto.
      apply Theorem49; split; auto; AssE x0.
Qed.

Lemma Lemma74 : forall x y,
  Ensemble x /\ Ensemble y ->
  ∪ \{ λ z, exists u, u∈x /\ z = [u] × y \} = x × y.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0, H1, H1.
    apply Axiom_Scheme in H2; destruct H2, H3, H3.
    rewrite H4 in H1; PP H1 a b.
    apply Axiom_SchemeP in H5; destruct H5, H6.
    apply Axiom_SchemeP; repeat split; auto.
    apply Axiom_Scheme in H6; destruct H6 as [_ H6].
    AssE x1; apply Theorem19 in H8.
    rewrite <- H6 in H3; auto.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1, H2.
    apply Axiom_Scheme; split; auto.
    exists (([a]) × y); split; AssE a.
    + apply Axiom_SchemeP; repeat split; auto.
      apply Axiom_Scheme; intros; auto.
    + apply Axiom_Scheme; split.
      * apply Theorem73; split; try apply H; auto.
      * exists a; split; auto.
Qed.

Theorem Theorem74 : forall x y,
  Ensemble x /\ Ensemble y -> Ensemble x × y.
Proof.
  intros; double H; double H0; destruct H0.
  apply Ex_Lemma74 in H; destruct H, H, H3.
  rewrite <- H3 in H0; apply Axiom_Substitution in H0; auto.
  rewrite H4 in H0; apply Axiom_Amalgamation in H0.
  rewrite Lemma74 in H0; auto.
Qed.

Hint Resolve Theorem74 : set.


(* 75 Theorem  If f is a function and domain f is a set, then f is a set. *)

Theorem Theorem75 : forall f,
  Function f /\ Ensemble dom( f ) -> Ensemble f.
Proof.
  intros; destruct H.
  assert (Ensemble ran(f)); try apply Axiom_Substitution; auto.
  assert (Ensemble (dom(f) × ran(f))).
  { apply Theorem74; split; auto. }
  apply Theorem33 with (x:=(dom( f ) × ran( f ))); auto.
  unfold Subclass; intros; rewrite Theorem70 in H3; auto.
  PP H3 a b; rewrite <- Theorem70 in H4; auto; AssE [a,b].
  repeat split; auto; apply Axiom_SchemeP; split; auto.
  generalize (Property_dom a b f H4); intro.
  generalize (Property_ran a b f H4); intro; tauto.
Qed.

Hint Resolve Theorem75 : set.


(* 76 Definition  Exponent y x = { f : f is a function, domain f = x and
   range f ⊂ y }. *)

Definition Exponent y x : Class :=
  \{ λ f, Function f /\ dom( f ) = x /\ ran( f ) ⊂ y \}.

Hint Unfold Exponent : set.


(* 77 Theorem  If x and y are sets so is Exponent y x. *)

Theorem Theorem77 : forall x y,
  Ensemble x /\ Ensemble y -> Ensemble (Exponent y x).
Proof.
  intros; apply Theorem33 with (x:=(pow(x × y))).
  - apply Theorem38; auto; apply Theorem74; auto.
  - unfold Subclass; intros; apply Theorem38.
    + apply Theorem74; auto.
    + apply Axiom_Scheme in H0; destruct H0, H1, H2.
    unfold Subclass; intros; rewrite Theorem70 in H4; auto.
    PP H4 a b; rewrite <- Theorem70 in H5; auto.
    AssE [a,b]; apply Axiom_SchemeP; split; auto.
    generalize (Property_dom a b z H5); intro; rewrite H2 in H7.
    generalize (Property_ran a b z H5); intro.
    unfold Subclass in H3; apply H3 in H8; split; auto.
Qed.

Hint Resolve Theorem77 : set.


(* 78 Definition  f is on x if and only if f is a function and x = domain f. *)

Definition On f x : Prop := Function f /\ dom( f ) = x.

Hint Unfold On : set.


(* 79 Definition  f is to y if and only if f is a function and rang f ⊂ y. *)

Definition To f y : Prop := Function f /\ ran(f) ⊂ y.

Hint Unfold To : set.


(* 80 Definition  f is onto y if and only if f is a function and range f = y. *)

Definition Onto f y : Prop := Function f /\ ran(f) = y.

Hint Unfold Onto : set.


End Fun.

Export Fun.

