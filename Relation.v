(* Basic properties of relations *)
Definition relation (X : Type) := X -> X -> Prop.

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Definition irreflexive {X : Type} (R : relation X) :=
  forall a : X, not (R a a).

Definition total {X : Type} (R : relation X) :=
  forall a b : X, (R a b) \/ (a = b) \/ (R b a).

Definition reverse_relation {X : Type} (R : relation X) : relation X :=
  fun a b : X => R b a.

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, R a b -> R b a.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Structure EquivRelation (X : Type) := mkEquivRelation {
  actual_relation :> relation X;
  eq_transitive : transitive actual_relation;
  eq_reflexive : reflexive actual_relation;
  eq_symmetric : symmetric actual_relation;
}.