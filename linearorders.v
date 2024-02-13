From LO Require Export Relation. 

(* Define what a linear order is *)
Structure LinearOrder : Type := mkLinearOrder
{ set :> Type;
lt : relation set;
lt_transitive : transitive lt;
lt_irreflexive : irreflexive lt;
lt_total : total lt;
}.

Arguments lt {_}.
Arguments lt_transitive {_} {_} {_} {_}.
Arguments lt_irreflexive {_}.

Notation "x < y" := (lt x y).
Notation "x <= y" := (x < y \/ x = y).

(* Basic properties of linear orders *)
Theorem lt_not_eq : forall {X : LinearOrder}, forall {a b : X}, a < b -> a <> b.
Proof.
intros. unfold not. intros. rewrite H0 in H. exact (lt_irreflexive b H).
Qed.

Theorem lt_not_gt : forall {X : LinearOrder}, forall {a b : X}, a < b -> ~(b < a).
Proof.
unfold not. intros. assert (a < a). { exact (lt_transitive H H0). }
assert (~a<a). { exact (lt_irreflexive a). }
contradiction.
Qed.

(* Defining minimum and maximum for linear orders *)
Definition is_minimum {X : LinearOrder} (x : X) := forall y : X, x < y \/ x = y.
Definition has_minimum (X : LinearOrder) := exists x : X, is_minimum x.

Definition is_maximum {X : LinearOrder} (x : X) := forall y : X, y < x \/ y = x.
Definition has_maximum (X : LinearOrder) := exists x : X, is_maximum x.
















