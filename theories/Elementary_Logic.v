Require Export Classical.

(* ELEMENTARY LOGIC *)

Module Logic.

Proposition Lemma_x : forall x: Prop, x -> x /\ x.
Proof. intros; split; auto. Qed.

Ltac double H := apply Lemma_x in H; destruct H.

Proposition Lemma_xy : forall (x y: Prop), x -> y -> x /\ y.
Proof. intros; split; auto. Qed.

Ltac add y H:= apply (Lemma_xy _ y) in H; auto.

Proposition definition_not : forall A B, (A<->B) -> (~ A) -> (~ B).
Proof. intros; destruct H; apply imply_to_or in H1; destruct H1; tauto. Qed.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Hint Resolve Lemma_x Lemma_xy : set.


End Logic.

Export Logic.

