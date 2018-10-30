Require Export A_0.

(* A.1 分类公理图式 *)

Module A1.

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


End A1.

Export A1.