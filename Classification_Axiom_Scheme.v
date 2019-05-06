Require Export Elementary_Logic.

(* THE CLASSIFICATION AXIOM SCHEME *)

Module Classification.

(* 定义初始 " 类 (Class) " ，元素和集合的类型都是 Class *)

Parameter Class : Type.


(* ∈：属于 x∈y : In x y *)

Parameter In : Class -> Class -> Prop.

Notation "x ∈ y" := (In x y) (at level 10).


(* 外延公理I  对于每个x与y，x=y成立之充分必要条件是对每一个z当且仅当z∈x时，z∈y *)

Axiom AxiomI : forall (x y: Class),
  x = y <-> (forall z: Class, z∈x <-> z∈y).

Hint Resolve AxiomI : set.


(* 定义1  x为一集当且仅当对于某一y，x∈y *)

Definition Ensemble (x: Class) : Prop := exists y: Class, x∈y.

Ltac Ens := unfold Ensemble; eauto.

Ltac AssE x := assert (Ensemble x); Ens.

Hint Unfold Ensemble : set.


(* {...:...} *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).


(* 分类公理II  *)

Axiom AxiomII : forall (b: Class) (P: Class -> Prop),
  b ∈ \{ P \} <-> Ensemble b /\ (P b).

Hint Resolve AxiomII : set.


End Classification.

Export Classification.

