Require Export Classical.

(* A.0 基本逻辑 *)

Module Property.

Proposition Lemma_xy : forall (x y: Prop), x -> y -> x /\ y.
Proof. intros; split; auto. Qed.

Proposition Lemma_x : forall x: Prop, x -> x /\ x.
Proof. intros; split; auto. Qed.

Proposition definition_not : forall A B, (A<->B) -> (~ A) -> (~ B).
Proof. unfold not; intros; apply H in H1; apply H0 in H1; auto. Qed.

Ltac double H := apply Lemma_x in H; destruct H.

Ltac add y H:= apply (Lemma_xy _ y) in H; auto.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Hint Resolve Lemma_xy Lemma_x definition_not : set.


End Property.

Export Property.

