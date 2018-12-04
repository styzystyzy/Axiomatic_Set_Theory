Require Export A_3.

(*A.4 集的存在性 *)

Module A4.

(* 子集公理III 如果x是一个集，存在一个集y使得对于每个z，假定z⊂x，则z∈y *)

Axiom AxiomIII : forall (x: Class),
  Ensemble x -> exists y, Ensemble y /\ (forall z, z⊂x -> z∈y).

Hint Resolve AxiomIII : set.


(* 定理33  如果x是一个集同时z⊂x，则z是一个集 *)

Theorem Theorem33 : forall x z,
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros; apply AxiomIII in H; destruct H.
  apply H in H0; Ens.
Qed.

Hint Resolve Theorem33 : set.


(* 定理34  0=∩μ同时∪μ =μ *)

Theorem Theorem34 : Φ = ∩μ.
Proof.
  intros; apply AxiomI; split; intros.
  - generalize (Theorem16 z); contradiction.
  - apply AxiomII in H; destruct H; apply H0.
    apply Theorem19; generalize (Theorem26 z); intros.
    apply Theorem33 in H1; auto.
Qed.

Theorem Theorem34' : μ = ∪μ.
Proof.
  apply AxiomI; split; intros.
  - apply Lemma_x in H; destruct H; apply AxiomII in H.
    destruct H; apply AxiomII; split; try auto.
    generalize (AxiomIII z H); intros.
    destruct H2; destruct H2; exists x; split.
    + apply H3; unfold Included; auto.
    + apply Theorem19; auto.
  - apply AxiomII in H; destruct H; apply Theorem19; auto.
Qed.

Hint Rewrite Theorem34 Theorem34' : set.


(* 定理35  如果x≠0，则∩x是一个集 *)

Lemma Lemma35 : forall x, x ≠ Φ <-> exists z, z∈x.
Proof.
  intros; assert (x = Φ <-> ~ (exists y, y∈x)).
  { split; intros.
    - intro; destruct H0; rewrite H in H0.
      apply AxiomII in H0; destruct H0; case H1; auto.
    - apply AxiomI; split; intros.
      + elim H; exists z; auto.
      + generalize (Theorem16 z); contradiction. }
  split; intros.
  - apply definition_not with (B:= ~(exists y, y∈x)) in H0; auto.
    apply NNPP in H0; destruct H0; exists x0; auto.
  - apply definition_not with (A:=(~ (exists y, y∈x))); auto.
    destruct H; split; auto.
Qed.

Theorem Theorem35 : forall x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros; apply Lemma35 in H; destruct H; AssE x0.
  generalize (Theorem32 x0 x H); intros.
  destruct H1; apply Theorem33 in H2; auto.
Qed.

Hint Resolve Lemma35 Theorem35 : set.


(* 定义36  pow(x)={y:y⊂x} *)

Definition PowerSet x : Class := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerSet x) (at level 0, right associativity).

Hint Unfold PowerSet : set.


(* 定理37  u=pow(u) *)

Theorem Theorem37 : μ = pow(μ).
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII; split; Ens; apply Theorem26'.
  - apply AxiomII in H; destruct H; apply Theorem19; auto.
Qed.

Hint Rewrite Theorem37 : set.


(* 定理38  如果x是一个集,则pow(x)是一个集*)

Theorem Theorem38 : forall x y,
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros; split.
  - apply AxiomIII in H; destruct H, H.
    assert (pow(x) ⊂ x0).
    { unfold Included; intros; apply AxiomII in H1.
      destruct H1; apply H0 in H2; auto. }
    apply Theorem33 in H1; auto.
  - split; intros.
    + apply Theorem33 with (z:=y) in H; auto.
      apply AxiomII; split; auto.
    + apply AxiomII in H0; apply H0.
Qed.

Hint Resolve Theorem38 : set.


(* 定理39  μ不是一个集 *)

(* 一个不是集的类 *)

Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  generalize (classic (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \})).
  intros; destruct H.
  - double H; apply AxiomII in H; destruct H; contradiction.
  - intro; elim H; apply AxiomII; split; auto.
Qed.

Theorem Theorem39 : ~ Ensemble μ.
Proof.
  unfold not; generalize Lemma_N; intros.
  generalize (Theorem26' \{ λ x, x ∉ x \}); intros.
  apply Theorem33 in H1; auto.
Qed.

Hint Resolve Lemma_N Theorem39 : set.


(* 定义40  [x]={z:如果x∈μ，则z=x} *)

Definition Singleton x : Class := \{ λ z, x∈μ -> z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Hint Unfold Singleton : set.


(* 定理41  如果x是一个集，则对于每个y，y∈[x]当且仅当y=x *)

Theorem Theorem41 : forall x, Ensemble x -> (forall y, y∈[x] <-> y=x).
Proof.
  intros; split; intros.
  - apply AxiomII in H0; destruct H0; apply H1.
    apply Theorem19 in H; auto.
  - apply AxiomII; split; intros; auto.
    rewrite <- H0 in H; auto.
Qed.

Hint Resolve Theorem41 : set.


(* 定理42  如果x是一个集，则[x]是一个集 *)

Theorem Theorem42 : forall x, Ensemble x -> Ensemble [x].
Proof.
  intros; double H; apply Theorem33 with (x:= pow(x)).
  - apply Theorem38 with (y:=x) in H0; destruct H0; auto.
  - unfold Included; intros.
    apply Theorem38 with (y:=z) in H0; destruct H0.
    apply H2; apply AxiomII in H1; destruct H1.
    apply Theorem19 in H; apply H3 in H.
    rewrite H; unfold Included; auto.
Qed.

Hint Resolve Theorem42 : set.


(* 定理43  [x]=μ当且仅当x不是一个集*)

Theorem Theorem43 : forall x, [x] = μ <-> ~ Ensemble x.
Proof.
  split; intros.
  - unfold not; intros; apply Theorem42 in H0.
    rewrite H in H0; generalize Theorem39; contradiction.
  - generalize (Theorem19 x); intros.
    apply definition_not with (B:= x∈μ) in H; try tauto.
    apply AxiomI; split; intros.
    * apply AxiomII in H1; destruct H1; apply Theorem19; auto.
    * apply AxiomII; split; try contradiction.
      apply Theorem19 in H1; auto.
Qed.

Hint Rewrite Theorem43 : set.


(* 定理42'  如果[x]是一个集，则x是一个集 *)

Theorem Theorem42' : forall x, Ensemble [x] -> Ensemble x.
Proof.
  intros.
  generalize (classic (Ensemble x)); intros.
  destruct H0; auto; generalize (Theorem39); intros.
  apply Theorem43 in H0; auto.
  rewrite H0 in H; contradiction.
Qed.

Hint Resolve Theorem42' : set.


(* 定理44  如果x是一个集，则∩[x]=x同时∪[x]=x；如果x不是一个集，则∩[x]=0同时∪[x]=u *)

Theorem Theorem44 : forall x, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  intros; generalize (Theorem41 x H); intros.
  split; apply AxiomI.
  - split; intros.
    + apply AxiomII in H1; destruct H1; apply H2; apply H0; auto.
    + apply AxiomII; split; Ens; intros.
      apply H0 in H2; rewrite H2; auto.
  - split; intros.
    + apply AxiomII in H1; destruct H1, H2, H2.
      unfold Singleton in H3; apply AxiomII in H3; destruct H3.
      rewrite H4 in H2; auto; apply Theorem19; auto.
    + apply AxiomII; split; Ens; exists x; split; auto.
      unfold Singleton; apply AxiomII; auto.
Qed.

Theorem Theorem44' : forall x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros; apply Theorem43 in H; split; rewrite H.
  - rewrite Theorem34; auto.
  - rewrite <- Theorem34'; auto.
Qed.

Hint Resolve Theorem44 Theorem44' : set.


(* 并的公理IV 如果x是一个集同时y是一个集，则x∪y也是一个集*)

Axiom AxiomIV : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble (x∪y).

Corollary AxiomIV': forall x y,
  Ensemble (x∪y) -> Ensemble x /\ Ensemble y.
Proof.
  intros; split.
  - assert (x ⊂ (x∪y)).
    { unfold Included; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
  - assert (y ⊂ (x∪y)).
    { unfold Included; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
Qed.

Hint Resolve AxiomIV AxiomIV' : set.


(* 定义45  [x|y]=[x]∪[y] *)

Definition Unordered x y : Class := [x]∪[y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

Hint Unfold Unordered : set.


(* 定理46  如果x是一个集同时y是一个集，则[x|y]是一个集，同时z∈[x|y] 当且仅当 z=x或者z=y;
          [x|y]=μ 当且仅当 x不是一个集或者y不是一个集 *)

Theorem Theorem46 : forall x y z,
  Ensemble x /\ Ensemble y -> Ensemble [x|y] /\ (z∈[x|y] <-> (z=x \/ z=y)).
Proof.
  split; intros; destruct H.
  - apply Theorem42 in H; apply Theorem42 in H0; apply AxiomIV; auto.
  - split; intros.
    + apply AxiomII in H1; destruct H1.
      destruct H2; apply AxiomII in H2; destruct H2.
      * left; apply H3; apply Theorem19; auto.
      * right; apply H3; apply Theorem19; auto.
    + apply AxiomII; split.
      * destruct H1; try rewrite <- H1 in H; auto.
        rewrite <- H1 in H0; auto.
      * destruct H1.
        -- left; apply AxiomII; split; rewrite <- H1 in H; auto.
        -- right; apply AxiomII; split; rewrite <- H1 in H0; auto.
Qed.

Theorem Theorem46' : forall x y, [x|y] = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  unfold Unordered; split; intros.
  - generalize (Theorem43 ([x] ∪ [y])); intros.
    destruct H0; rewrite H in H0.
    assert ([μ] = μ); try apply Theorem43; try apply Theorem39.
    apply H0 in H2; rewrite <- H in H2.
    assert (Ensemble([x]∪[y]) <-> Ensemble [x] /\ Ensemble [y]).
    { split; try apply AxiomIV; try apply AxiomIV'. }
    apply definition_not in H3; auto.
    generalize (not_and_or (Ensemble [x]) (Ensemble [y])); intros.
    apply H4 in H3; destruct H3.
    + assert (Ensemble [x] <-> Ensemble x).
      { split; try apply Theorem42'; try apply Theorem42; auto. }
      apply definition_not in H5; auto.
    + assert (Ensemble [y] <-> Ensemble y).
      { split; try apply Theorem42'; try apply Theorem42; auto. }
      apply definition_not in H5; auto.
  - destruct H; apply Theorem43 in H; rewrite H; try apply Theorem20.
    generalize (Theorem6 μ [y]); intros; rewrite H0; apply Theorem20.
Qed.

Hint Resolve Theorem46 Theorem46' : set.


(* 定理47  如果x与y是两个集，则∩[x|y]=x∩y同时∪[x|y]=x∪y; 如果x或者y不是一个集，则∩[x|y]=0同时∪[x|y]=u *)

Theorem Theorem47 : forall x y,
  Ensemble x /\ Ensemble y -> (∩[x|y] = x ∩ y) /\ (∪[x|y] = x ∪ y).
Proof.
  intros; split; apply AxiomI; intros.
  - split; intros.
    + apply Theorem4'.
      split; apply AxiomII in H0; destruct H0; apply H1; apply Theorem4.
      * left; apply AxiomII; split; try apply H; auto.
      * right; apply AxiomII; split; try apply H; auto.
    + apply Theorem4' in H0; destruct H0.
      apply AxiomII; split; intros; try AssE z.
      apply Theorem4 in H2; destruct H2.
      * apply AxiomII in H2; destruct H2; destruct H.
        apply Theorem19 in H; apply H4 in H; rewrite H; auto.
      * apply AxiomII in H2; destruct H2; destruct H.
        apply Theorem19 in H5; apply H4 in H5; rewrite H5; auto.
  - split; intros.
    + apply AxiomII in H0; destruct H0; destruct H1; destruct H1.
      apply Theorem4 in H2; apply Theorem4.
      destruct H2; apply AxiomII in H2; destruct H2.
      * left; destruct H; apply Theorem19 in H.
        apply H3 in H; rewrite H in H1; auto.
      * right; destruct H; apply Theorem19 in H4.
        apply H3 in H4; rewrite H4 in H1; auto.
    + apply Theorem4 in H0; apply AxiomII.
      split; destruct H0; try AssE z.
      * exists x; split; auto; apply Theorem4; left.
        apply AxiomII; split; try apply H; trivial.
      * exists y; split; auto; apply Theorem4; right.
        apply AxiomII; split; try apply H; trivial.
Qed.

Theorem Theorem47' : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> (∩[x|y] = Φ) /\ (∪[x|y] = μ).
Proof.
  intros; split; apply Theorem46' in H; rewrite H.
  - rewrite Theorem34; auto.
  - rewrite <- Theorem34'; auto.
Qed.

Hint Resolve Theorem47 Theorem47' : set.


End A4.

Export A4.


