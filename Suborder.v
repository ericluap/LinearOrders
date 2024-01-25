From LO Require Export Embedding.
Require Import Classical.

(* Definition of a suborder of a linear order *)
Structure Suborder (Y : LinearOrder) : Type := mkSuborder
{
actual_order :> LinearOrder;
embedding : Embedding actual_order Y;
}.

Arguments embedding {_} {_}.

(* Every linear order is a suborder of itself *)
Definition id_suborder (X : LinearOrder) : Suborder X :=
{|
  actual_order := X;
  embedding := id_embedding X;
|}.

Definition suborder_suborder (X : LinearOrder) (Y : Suborder X) (Z : Suborder Y) : Suborder X :=
{|
  actual_order := Z;
  embedding := embedding_embedding Z.(embedding _) Y.(embedding _);
|}.

Definition Image {X Y : Type} (f : X -> Y) := {y : Y | exists x : X, f x = y}.
 
Theorem same_proj1 : forall A : Type, forall P : A -> Prop,
forall (a b : {n : A | P n}), proj1_sig a = proj1_sig b -> a = b.
Proof.
intros. destruct a. destruct b. simpl in H.
subst. f_equal. apply proof_irrelevance.
Qed.

(* Defintion of a well order *)
Definition well_order (X : LinearOrder) :=
forall A : Suborder X, (A -> has_minimum A).

(* Proving that every suborder of a well order is well ordered *)
Theorem suborder_of_well_order : 
forall Y : LinearOrder, forall X : Suborder Y, well_order Y -> well_order X.
Proof.
intros. unfold well_order in *. intros. 
specialize (H (suborder_suborder Y X A) X0) as H1.
simpl in H1. assumption.
Qed.