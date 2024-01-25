From LO Require Export Embedding.
Require Import Description.

(* Definition of isomorphism between two linear orders *)
Structure Isomorphism (X Y : LinearOrder) : Type := mkIsomorphism
{
iso :> Embedding X Y;
surjective_map : forall y : Y, exists x : X, iso x = y;
}.

Definition isomorphic (X Y : LinearOrder) : Prop := exists _ : Isomorphism X Y, True.

Notation "X ~= Y" := (isomorphic X Y) (at level 100) : type_scope.

(* The identity map is an isomorphism *)
Theorem id_embedding_surjective (X : LinearOrder) :
forall y : X, exists x : X, id_embedding _ x = y.
Proof.
intros. exists y. unfold id_embedding. simpl. unfold id_embedding_map. reflexivity.
Qed.

Definition id_isomorphism (X : LinearOrder) : Isomorphism X X :=
{|
  iso := id_embedding X;
  surjective_map := id_embedding_surjective X;
|}. 

(* Proving properties about isomorphisms *)
Theorem iso_reflexive (X : LinearOrder) : X ~= X.
Proof.
exists (id_isomorphism X). reflexivity.
Qed.

(* thank you to https://stackoverflow.com/questions/62464821/how-to-make-an-inverse-function-in-coq *)
Theorem iso_inverse {X Y : LinearOrder} (f : Isomorphism X Y) : 
exists (g : Isomorphism Y X), (forall x : X, g (f x) = x) /\ (forall y : Y, f (g y) = y).
Proof.
assert (forall y : Y, exists! z : X, f z = y).
{ intros. destruct (surjective_map X Y f y).
exists x. split. assumption. intros. apply (@order_preserving_injective X Y f).
rewrite H, H0. reflexivity. }
assert (forall y : Y, {z : X | f z = y}).
{ intros. specialize (H y). exact (constructive_definite_description _ H). }
assert (forall a b : Y, a < b -> (fun y : Y => proj1_sig (X0 y)) a < (fun y : Y => proj1_sig (X0 y)) b).
{ intros. apply (@order_preserving_backwards X Y f). 
rewrite (proj2_sig (X0 a)). rewrite (proj2_sig (X0 b)). assumption. }
assert (forall z : X, exists y : Y, (fun t : Y => proj1_sig (X0 t)) y = z).
{ intros. exists (f z). specialize (proj2_sig (X0 (f z))). simpl.
exact (@order_preserving_injective X Y f (proj1_sig (X0 (f z))) z). }
exists ({|
  iso := {|
    map := (fun y : Y => proj1_sig (X0 y));
    order_preserving := H0;
  |};
  surjective_map := H1;
|}).
split.
- simpl. intros. specialize (proj2_sig (X0 (f x))) as H2. simpl in H2.
exact (@order_preserving_injective X Y f (proj1_sig (X0 (f x))) x H2).
- simpl. intros. exact (proj2_sig (X0 y)).
Qed.

Theorem iso_symmetric (X Y : LinearOrder) : (X ~= Y) -> (Y ~= X).
Proof.
intros. unfold isomorphic in *. destruct H.
specialize (iso_inverse x) as H1. destruct H1.
exists x0. trivial.
Qed.

Theorem iso_transitive (X Y Z : LinearOrder) : (X ~= Y) -> (Y ~= Z) -> (X ~= Z).
Proof.
intros. unfold isomorphic in *. destruct H as [x_to_y]. destruct H0 as [y_to_z].
assert (forall z : Z, exists x : X, (embedding_embedding x_to_y y_to_z) x = z).
{ intros. destruct (surjective_map Y Z y_to_z z). destruct (surjective_map _ _ x_to_y x).
exists x0. simpl. unfold embedding_embedding_map. rewrite <- H1. rewrite H2. reflexivity. }
exists {|
  iso := (embedding_embedding x_to_y y_to_z);
  surjective_map := H1;
|}. trivial.
Qed.