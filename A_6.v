Require Export A_5.

(* A.6 函数 *)

Module A6.

(* 定义63 f是一个函数当且仅当f是一个关系同时对每个x，每个y，每个z，如果[x,y]∈f且[x，z]∈f,则y=z*)

Definition Function f : Prop :=
  Relation f /\ (forall x y z, [x,y] ∈ f /\ [x,z] ∈ f -> y=z).

Hint Unfold Function : set.


(* 定理64 如果f是一个函数同时g是一个函数，则 f。g 也是一个函数 *)

Theorem Theorem64 : forall f g,
  Function f /\ Function g -> Function (f ∘ g).
Proof.
  intros; destruct H.
  unfold Function; split; intros.
  - unfold Relation; intros; PP H1 a b; eauto.
  - destruct H1; apply AxiomII_P in H1; apply AxiomII_P in H2.
    destruct H1, H2, H3, H4, H3, H4.
    unfold Function in H, H0; destruct H; destruct H0.
    assert (x0=x1). { apply H8 with x; split; auto. }
    rewrite H9 in H5; apply H7 with x1; split; auto.
Qed.

Hint Resolve Theorem64 : set.


(* 定义65 f的定义域={x：对于某个y，[x，y]∈f} *)

Definition Domain f : Class := \{ λ x, exists y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

Corollary Property_dom : forall x y f,
  [x,y] ∈ f -> x ∈ dom( f ).
Proof.
  intros; unfold Domain; apply AxiomII; split; eauto.
  AssE [x,y]; apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Domain : set.


(* 定义66 f的值域={y：对于某个x，[x，y]∈f} *)

Definition Range f : Class := \{ λ y, exists x:Class, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

Corollary Property_ran : forall x y f,
  [x,y] ∈ f -> y ∈ ran( f ).
Proof.
  intros; apply AxiomII.
  split; eauto; AssE [x,y].
  apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Range : set.


(* 定理67 μ的定义域=μ同时μ的值域=μ *)

Theorem Theorem67 : dom( μ ) = μ /\ ran( μ ) = μ.
Proof.
  intros; split; apply AxiomI; split; intros.
  - AssE z; apply Theorem19; auto.
  - apply Theorem19 in H.
    unfold Domain; apply AxiomII; split; auto.
    exists z; apply Theorem19.
    apply Theorem49; split; auto.
  - AssE z; apply Theorem19; auto.
  - apply Theorem19 in H.
    unfold Range; apply AxiomII; split; auto.
    exists z; apply Theorem19.
    apply Theorem49; split; auto.
Qed.

Hint Rewrite Theorem67 : set.


(* 定义68 f(x)=∩{y:[x,y]∈f} *)

Definition Value f x : Class := ∩ \{ λ y, [x,y] ∈ f \}.

Notation "f [ x ]" := (Value f x)(at level 5).

Hint Unfold Value : set.


(* 值的性质 一 *)

Corollary Property_Value : forall f x,
  Function f -> x ∈ dom( f ) -> [x,f[x]] ∈ f.
Proof.
  intros; unfold Function in H;destruct H as [_ H].
  apply AxiomII in H0; destruct H0, H1.
  assert (x0=f[x]).
  - apply AxiomI; split; intros.
    + apply AxiomII; split; intros; try Ens.
       apply AxiomII in H3; destruct H3.
       assert (x0=y). { apply H with x; split; auto. }
       rewrite <- H5; auto.
    + apply AxiomII in H2; destruct H2 as [_ H2].
       apply H2; apply AxiomII; split; auto.
       AssE [x, x0]; apply Theorem49 in H3; apply H3.
  - rewrite <- H2; auto.
Qed.

(* 定理69 如果x∉f的定义域，则f[x]=μ;如果x∈f的定义域，则f[x]∈μ*)

Lemma Lemma69 : forall x f,
  Function f -> ( x ∉ dom( f ) -> \{ λ y, [x,y] ∈ f \} = Φ ) /\
  ( x ∈ dom( f ) -> \{ λ y, [x,y] ∈ f \} <> Φ ).
Proof.
  intros; split; intros.
  - generalize (classic (\{ λ y0, [x, y0] ∈ f \} = Φ)); intro. 
    destruct H1; auto; apply Lemma35 in H1; auto.
    elim H1; intro z; intros; apply AxiomII in H2.
    destruct H2 as [H2 H3]; apply Property_dom in H3; contradiction.
  - apply Lemma35; auto; exists f[x].
    apply AxiomII;eapply Property_Value in H0; auto.
    split; auto; apply Property_ran in H0; Ens.
Qed.

Theorem Theorem69 : forall x f,
  ( x ∉ (dom( f )) -> f[x] = μ ) /\ ( x ∈ dom( f ) -> (f[x]) ∈  μ ).
Proof.
  intros; split; intros.
  - assert (\{ λ y, [x,y] ∈ f \} = Φ).
    { apply AxiomI; split; intros.
       apply AxiomII in H0; destruct H0.
       apply Property_dom in H1; contradiction.
       generalize (Theorem16 z); intro; contradiction. }
    unfold Value; rewrite H0; apply Theorem24.
  - assert (\{ λ y, [x,y] ∈ f \} <> Φ).
    { intro.
       apply AxiomII in H; destruct H, H1.
       generalize (AxiomI \{ λ y : Class,[x, y] ∈ f \} Φ); intro; destruct H2.
       apply H2 with x0 in H0; destruct H0.
       assert (x0 ∈ Φ).
       { apply H0; apply AxiomII; split; auto.
          AssE [x, x0];  apply Theorem49 in H5; tauto. }
       eapply Theorem16; eauto. }
     apply Theorem35 in H0; apply Theorem19; auto.
Qed.

Hint Resolve Theorem69 : set.


(* 值的性质 二 *)

Corollary Property_Value' : forall f x,
  Function f -> f[x] ∈ ran(f) -> [x,f[x]] ∈ f.
Proof.
  intros; apply Property_Value; auto.
  apply AxiomII in H0; destruct H0, H1.
  generalize (classic (x ∈ dom( f))); intros.
  destruct H2; auto; apply Theorem69 in H2; auto.
  rewrite H2 in H0; generalize (Theorem39); intro; contradiction.
Qed.

(* 定理70 如果f是一个函数，则f={[x,y]:y=f[x]} *)

Theorem Theorem70 : forall f,
  Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; apply AxiomI; split; intros.
  - PP' H1 a b; apply AxiomII_P; split; try Ens.
    apply AxiomI; split; intros.
    + apply AxiomII; split; intros; try Ens.
      apply AxiomII in H3; destruct H3.
      apply Lemma_xy with (y:=[a, y] ∈ f) in H0; auto.
      unfold Function in H; apply H in H0.
      rewrite <- H0; auto.
    + unfold Element_I in H1; apply AxiomII in H2; destruct H2.
      apply H3; apply AxiomII; split; auto; AssE [a,b].
      apply Theorem49 in H4; try apply H4.
  - PP H0 a b; apply AxiomII_P in H1; destruct H1.
    generalize (classic (a ∈ dom( f ))); intros; destruct H3.
    + apply Property_Value in H3; auto; rewrite H2; auto.
    + apply Theorem69 in H3; auto.
      rewrite H3 in H2; rewrite H2 in H1.
      apply Theorem49 in H1; destruct H1 as [_ H1].
      generalize Theorem39; intro; contradiction.
Qed.

Hint Resolve Theorem70 : set.


(* 定理71 如果f和g都是函数，则f=g的充要条件是对于每个x，f[x]=g[x] *)

Theorem Theorem71 : forall f g,
  Function f /\ Function g -> (f = g <-> forall x, f[x] = g[x]).
Proof.
  intros; split; intros; try rewrite H0; trivial.
  destruct H; intros; apply (Theorem70 f) in H; apply (Theorem70 g) in H1.
  rewrite H; rewrite H1; apply AxiomI; split; intros;
  PP' H3 a b; AssE [a,b]; apply AxiomII_P; apply AxiomII_P in H2.
  - rewrite <- H0; split; tauto.
  - rewrite -> H0; split; tauto.
Qed.

Hint Resolve Theorem71 : set.


(* 代换公理 V 如果f是一个函数同时f的定义域是一个集，则f的值域是一个集 *)

Axiom AxiomV : forall f,
  Function f -> Ensemble dom(f) -> Ensemble ran(f).

Hint Resolve AxiomV : set.


(* 合并公理 VI 如果x是一个集，则 ∪x 也是一个集 *)

Axiom AxiomVI : forall x, Ensemble x -> Ensemble (∪ x).

Hint Resolve AxiomVI : set.


(* 定义72 x × y={[u,v]:u∈x/\v∈y} *)

Definition Cartesian x y : Class := \{\ λ u v, u∈x /\ v∈y \}\.

Notation "x × y" := (Cartesian x y)(at level 2, right associativity).

Hint Unfold Cartesian : set.


(* 定理73 如果u与y均为集，则[u]×y也是集*)

Lemma Ex_Lemma73 : forall u y, 
  Ensemble u /\ Ensemble y -> exists f, Function f /\ dom(f) = y /\ ran(f) = [u] × y.
Proof.
  intros; destruct H.
  exists (\{\ λ w z, (w∈y /\ z = [u,w]) \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; Ens.
  - destruct H1.
    apply AxiomII_P in H1; apply AxiomII_P in H2.
    destruct H1 as [_ [_ H1]]; destruct H2 as [_ [_ H2]].
    rewrite H2; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1 as [_ [t H1]].
      apply AxiomII_P in H1; tauto.
    + apply AxiomII; split; try Ens.
      exists [u,z]; apply AxiomII_P; split; auto.
      AssE z; apply Theorem49; split; auto.
      apply Theorem49; tauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1, H1, H2.
      apply AxiomII_P in H2; destruct H2, H3.
      rewrite H4; apply AxiomII_P; repeat split; auto.
      * apply Theorem49; split; auto; AssE x0.
      * apply AxiomII; split; auto.
    + PP H1 a b; apply AxiomII_P in H2; destruct H2, H3.
      apply AxiomII; split; auto; exists b.
      apply AxiomII_P; repeat split; auto.
      * apply Theorem49; split; auto; AssE b.
      * apply Theorem19 in H; apply AxiomII in H3.
        destruct H3; rewrite H5; auto.
Qed.

Theorem Theorem73 : forall u y,
  Ensemble u /\ Ensemble y -> Ensemble ([u] × y).
Proof.
  intros; elim H; intros; apply Ex_Lemma73 in H; auto.
  destruct H,H,H2; rewrite <- H3; apply AxiomV; auto.
  rewrite H2; auto.
Qed.

Hint Resolve Theorem73 : set.


(* 定理74 如果x与y均为集，则 x×y 也是集 *)

Lemma Ex_Lemma74 : forall x y,
  Ensemble x /\ Ensemble y -> exists f, Function f /\ dom( f ) = x 
  /\ ran( f ) = \{ λ z, (exists u, u∈x /\ z = [u] × y) \}.
Proof.
  intros; destruct H.
  exists (\{\ λ u z, (u∈x /\ z = [u] × y) \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; Ens.
  - destruct H1; apply AxiomII_P in H1; apply AxiomII_P in H2.
    destruct H1, H2, H3, H4; subst z; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1, H2.
      apply AxiomII_P in H2; tauto.
    + apply AxiomII; split; try AssE z.
      exists (([z]) × y); apply AxiomII_P.
      repeat split; auto; apply Theorem49; split; auto.
      apply Theorem73; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1, H2.
      apply AxiomII_P in H2; apply AxiomII.
      split; auto; exists x0; tauto.
    + apply AxiomII in H1; destruct H1, H2, H2.
      apply AxiomII; split; auto.
      exists x0; apply AxiomII_P; repeat split; auto.
      apply Theorem49; split; auto; AssE x0.
Qed.

Lemma Lemma74 : forall x y,
  Ensemble x /\ Ensemble y ->
  ∪ \{ λ z, (exists u, u∈x /\ z = [u] × y) \} = x × y.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H0; destruct H0, H1, H1.
    apply AxiomII in H2; destruct H2, H3, H3.
    rewrite H4 in H1; PP H1 a b.
    apply AxiomII_P in H5; destruct H5, H6.
    apply AxiomII_P; repeat split; auto.
    apply AxiomII in H6; destruct H6 as [_ H6].
    AssE x1; apply Theorem19 in H8.
    rewrite <- H6 in H3; auto.
  - PP H0 a b; apply AxiomII_P in H1; destruct H1, H2.
    apply AxiomII; split; auto.
    exists (([a]) × y); split; AssE a.
    + apply AxiomII_P; repeat split; auto.
      apply AxiomII; intros; auto.
    + apply AxiomII; split.
      * apply Theorem73; split; try apply H; auto.
      * exists a; split; auto.
Qed.

Theorem Theorem74 : forall x y, 
  Ensemble x /\ Ensemble y -> Ensemble x × y.
Proof.
  intros; double H; double H0; destruct H0.
  apply Ex_Lemma74 in H; destruct H, H, H3.
  rewrite <- H3 in H0; apply AxiomV in H0; auto.
  rewrite H4 in H0; apply AxiomVI in H0.
  rewrite Lemma74 in H0; auto.
Qed.

Hint Resolve Theorem74 : set.


(* 定理75 如果f是一个函数同时f的定义域是一个集，则f是一个集 *)

Theorem Theorem75 : forall f, 
  Function f /\ Ensemble dom( f ) -> Ensemble f.
Proof.
  intros; destruct H.
  assert (Ensemble ran(f)); try apply AxiomV; auto.
  assert (Ensemble (dom( f)) × (ran( f))).
  { apply Theorem74; split; auto. }
  apply Theorem33 with (x:=(dom( f ) × ran( f ))); auto.
  unfold Included; intros; rewrite Theorem70 in H3; auto.
  PP H3 a b; rewrite <- Theorem70 in H4; auto; AssE [a,b].
  repeat split; auto; apply AxiomII_P; split; auto.
  generalize (Property_dom a b f H4); intro.
  generalize (Property_ran a b f H4); intro; tauto.
Qed.

Hint Resolve Theorem75 : set.

(* 定义76 Exponent y x = {f:f是一个函数，f的定义域=x同时f的值域⊂ y} *)

Definition Exponent y x : Class :=
  \{ λ f, (Function f /\ dom( f ) = x /\ (ran( f )) ⊂ y) \}.

Hint Unfold Exponent : set.

(* 定理77 如果x与y均为集，则 Exponent y x 也是集*)

Theorem Theorem77 : forall x y,
  Ensemble x /\ Ensemble y -> Ensemble (Exponent y x).
Proof.
  intros; apply Theorem33 with (x:=(pow(x × y))).
  - apply Theorem38; auto; apply Theorem74; auto.
  - unfold Included; intros; apply Theorem38.
    + apply Theorem74; auto.
    + apply AxiomII in H0; destruct H0, H1, H2.
    unfold Included; intros; rewrite Theorem70 in H4; auto.
    PP H4 a b; rewrite <- Theorem70 in H5; auto.
    AssE [a,b]; apply AxiomII_P; split; auto.
    generalize (Property_dom a b z H5); intro; rewrite H2 in H7.
    generalize (Property_ran a b z H5); intro.
    unfold Included in H3; apply H3 in H8; split; auto.
Qed.

Hint Resolve Theorem77 : set.


(* 定义78 f在x上，当且仅当f为一函数同时x=f的定义域 *)

Definition On f x : Prop :=  (Function f /\ dom( f ) = x).

Hint Unfold On : set.


(* 定义79 f到y，当且仅当f是一个函数同时f的值域⊂y *)

Definition To f y : Prop := (Function f /\ (ran(f)) ⊂ y). 

Hint Unfold To : set.


(* 定义80 f到y上，当且仅当f是一个函数同时f的值域=y *)

Definition Onto f y : Prop := (Function f /\ ran(f) = y).

Hint Unfold Onto : set.


End A6.

Export A6.


