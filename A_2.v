Require Export A_1.

(* A.2 分类公理图式续 *)

Module A2.

(* {...:...} *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).


(* 分类公理II  *)

Axiom AxiomII : forall (b: Class) (P: Class -> Prop),
  b ∈ \{ P \} <-> Ensemble b /\ (P b).

Hint Resolve AxiomII : set.


End A2.

Export A2.