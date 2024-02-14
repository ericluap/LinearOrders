From LO Require Export linearorders.

(* Define what a (non-convex) embedding between linear orders is *)
Structure Embedding (X Y : LinearOrder) : Type := mkEmbedding
{
map :> X -> Y;
order_preserving : forall a b : X, a < b -> map a < map b
}.

Arguments map {_}.
Arguments order_preserving {_} {_} {_} {_} {_}.

Definition embedding_embedding_map {X Y Z: LinearOrder} (f : Embedding X Y) (g : Embedding Y Z)
: X -> Z := fun x : X => g (f x).

Theorem embedding_embedding_map_order_preserving {X Y Z: LinearOrder} (f : Embedding X Y) (g : Embedding Y Z)
: forall a b : X, a < b -> embedding_embedding_map f g a < embedding_embedding_map f g b.
Proof.
intros. unfold embedding_embedding_map. 
exact (order_preserving (order_preserving H)).
Qed.

Definition embedding_embedding {X Y Z : LinearOrder} (f : Embedding X Y) (g : Embedding Y Z) 
: Embedding X Z := {|
  map := embedding_embedding_map f g;
  order_preserving := embedding_embedding_map_order_preserving f g;
|}.

(* Definition of the identity embedding *)
Definition id_embedding_map {X : LinearOrder} := fun x : X => x.

Theorem id_embedding_map_order_preserving (X : LinearOrder) : 
forall a b : X, a < b -> id_embedding_map a < id_embedding_map b.
Proof.
intros. unfold id_embedding_map. assumption.
Qed.

Definition id_embedding (X : LinearOrder) : Embedding X X :=
{|
  map := id_embedding_map;
  order_preserving := id_embedding_map_order_preserving X;
|}.

(* Properties of order preserving maps *)
Theorem order_preserving_backwards : 
forall {X Y : LinearOrder}, 
forall {f : Embedding X Y},
forall {a b : X}, f a < f b -> a < b.
Proof.
intros. assert (a < b \/ a = b \/ b < a).
{ exact (X.(lt_total) a b). }
destruct H0.
- assumption.
- destruct H0.
  -- assert (f a <> f b). { exact (lt_not_eq H). }
     assert (f a = f b). { rewrite H0. reflexivity. }
     contradiction.
  -- assert (f b < f a). { exact (order_preserving H0). }
     assert (~ f b < f a). { exact (lt_not_gt H). }
     contradiction.
Qed.

Theorem order_preserving_injective :
forall {X Y : LinearOrder}, 
forall {f : Embedding X Y},
forall {a b : X}, f a = f b -> a = b.
Proof.
intros. assert (a < b \/ a = b \/ b < a). { exact (X.(lt_total) a b). }
destruct H0.
- assert (f a < f b). { exact (order_preserving H0). }
  assert (f a <> f b). { exact (lt_not_eq H1). }
  contradiction.
- destruct H0.
  -- assumption.
  -- assert (f b < f a). { exact (order_preserving H0). }
     assert (f b <> f a). { exact (lt_not_eq H1). }
     assert (f a <> f b). { unfold not. intros. symmetry in H3. contradiction. }
     contradiction.
Qed.
