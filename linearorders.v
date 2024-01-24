Require Import Classical.
Require Import Wf_nat.
Require Import FunctionalExtensionality.
Require Import Description.

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

(* Proving that < on the natural numbers satisfies the properties of a linear order *)
Theorem nat_lt_transitive : transitive Peano.lt.
Proof.
intros a b c hab hbc.
induction hbc as [| b' hb'c].
  apply le_S. exact hab.
  apply le_S. exact IHhb'c.
Qed.

Theorem nat_nlt_succ (x : nat) : ~(S x < x)%nat.
Proof.
unfold not. intros. induction x.
- inversion H.
- apply le_S_n in H. exact (IHx H).
Qed.

Theorem nat_lt_irreflexive : irreflexive Peano.lt.
Proof.
unfold Peano.lt. unfold irreflexive.
intros a ha.
induction a as [|c hc].
- inversion ha.
- apply le_S_n in ha. exact (hc ha).
Qed.

Theorem nat_lt_total : total Peano.lt.
Proof.
unfold Peano.lt. unfold total.
intros a b.
induction a as [|c hc].
induction b as [|d hd].
- right. left. trivial.
- destruct hd.
  --  apply le_S in H. left. exact H.
  --  destruct H.
    --- assert (1 = S d). rewrite H. reflexivity. left. rewrite H0. exact (le_n (S d)).
    --- inversion H.
- destruct hc.
  --  inversion H.
    --- right. left. reflexivity.
    --- apply le_n_S in H0. left. exact H0.
  --  destruct H.
    --- right. right. rewrite H. exact (le_n (S b)).
    --- apply le_S in H. right. right. exact H.
Qed.

(* The natural numbers as a linear order *)
Definition omega : LinearOrder :=
mkLinearOrder nat Peano.lt nat_lt_transitive nat_lt_irreflexive nat_lt_total.

(* Proving that the reverse of the relation of a linear order is still a linear order *)
Theorem reverse_transitive (X : LinearOrder) : transitive (reverse_relation X.(lt)).
Proof.
unfold reverse_relation. unfold transitive.
intros a b c hba hcb.
exact (lt_transitive hcb hba).
Qed.

Theorem reverse_irreflexive (X : LinearOrder) : irreflexive (reverse_relation X.(lt)).
Proof.
unfold reverse_relation. unfold irreflexive. intros a.
exact (X.(lt_irreflexive) a).
Qed.

Theorem reverse_total (X : LinearOrder) : total (reverse_relation X.(lt)).
Proof.
unfold reverse_relation. unfold total.
intros a b.
assert (H : b < a \/ b = a \/ a < b). exact (X.(lt_total) b a).
destruct H.
- left. exact H.
- destruct H.
  --  right. left. symmetry. exact H.
  --  right. right. exact H.
Qed.

(* Given a linear order X, `reverse X` reverses the ordering on X *)
Definition reverse (X : LinearOrder) : LinearOrder :=
mkLinearOrder 
  X 
  (reverse_relation X.(lt))
  (reverse_transitive X)
  (reverse_irreflexive X) 
  (reverse_total X).

(* omega_star is the natural numbers with the reverse ordering *)
Definition omega_star : LinearOrder := reverse omega.

(* Defining minimum and maximum for linear orders *)
Definition is_minimum {X : LinearOrder} (x : X) := forall y : X, x < y \/ x = y.
Definition has_minimum (X : LinearOrder) := exists x : X, is_minimum x.

Definition is_maximum {X : LinearOrder} (x : X) := forall y : X, y < x \/ y = x.
Definition has_maximum (X : LinearOrder) := exists x : X, is_maximum x.

(* Proving that properties about minimums and maximums for omega *)
Theorem zero_is_minimum : is_minimum (0 : omega).
Proof.
unfold is_minimum. intros. induction y.
- right. trivial.
- destruct IHy.
  --  apply le_S in H. left. assumption.
  --  left. assert (0 <= y). rewrite H. trivial. apply le_n_S in H0. assumption.
Qed.

Theorem not_lt_zero : forall a : omega, ~(a < 0).
Proof.
unfold not. intros.
assert ((0 : omega) < a \/ 0 = a). { exact (zero_is_minimum a). }
destruct H0.
- exact (lt_not_gt H H0).
- symmetry in H0. exact (lt_not_eq H H0).
Qed.

Theorem omega_has_minimum : has_minimum omega.
Proof.
unfold has_minimum. unfold is_minimum. exists 0. exact (zero_is_minimum).
Qed.

Theorem omega_no_maximum : ~ has_maximum omega.
Proof.
unfold has_maximum. unfold not. intros. destruct H.
unfold is_maximum in H. assert (S x < x \/ S x = x)%nat. exact (H (S x)). 
destruct H0.
- exact (nat_nlt_succ x H0).
- apply (n_Sn x). symmetry. exact H0.
Qed.

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

(* Proving that omega is a well-order *)
Theorem zero_in_image_least : 
forall A : Suborder omega, (exists a : A, embedding a = 0) -> has_minimum A.
Proof.
intros. destruct H. unfold has_minimum. exists x. unfold is_minimum. intros.
assert (embedding x < embedding y \/ embedding x = embedding y).
{ rewrite H. exact (zero_is_minimum (embedding y)). }
destruct H0.
- left. exact (order_preserving_backwards H0).
- right. exact (order_preserving_injective H0).
Qed.

Theorem less_than_1_is_0 : forall n : nat, (n < 1)%nat -> n = 0.
Proof.
intros. destruct n.
- trivial.
- unfold Peano.lt in H. apply le_S_n in H. contradiction (not_lt_zero _ H).
Qed.

Theorem prev_not_in_image_least :
forall A : Suborder omega,
(exists a : A, 
forall x : omega, x < embedding a -> forall b : A, embedding b <> x) ->
has_minimum A.
Proof. 
intros. destruct H. unfold has_minimum. exists x. unfold is_minimum.
intros. assert (x < y \/ x = y \/ y < x). { exact (A.(lt_total) x y). }
destruct H0.
- left. assumption.
- destruct H0.
* right. assumption.
* left. assert (embedding y < embedding x). 
{ exact (order_preserving H0) . }
assert (embedding y <> embedding y). { exact (H (embedding y) H1 y). }
contradiction.
Qed.

Theorem omega_well_order : well_order omega.
Proof.
destruct (classic (well_order omega)).
- assumption.
- unfold well_order in H. apply not_all_ex_not in H.
destruct H.
assert (forall n : omega, ~(exists a : x, embedding a = n)).
{ intros.
 induction n using (well_founded_induction lt_wf).
destruct (classic (exists a : x, embedding a = n)).
{ destruct H1. 
assert (exists a : x, 
forall z : omega, z < embedding a -> forall b : x, embedding b <> z).
{ exists x0. intros. subst. specialize (H0 z H2) as H3. firstorder. }
specialize (prev_not_in_image_least _ H2) as H3.
assert (x -> has_minimum x). { intros. assumption. }
contradiction (H H4). }
assumption. }
assert (x -> has_minimum x). 
{ intros. specialize (H0 (embedding X)) as H1. unfold not in H1.
assert (exists a : x, embedding a = embedding X).
{ exists X. reflexivity. }
contradiction. }
contradiction.
Qed.

(* Every suborder of omega is a well order *)
Theorem suborder_omega_well_order : forall X : Suborder omega, well_order X.
Proof.
intros. exact (suborder_of_well_order omega X omega_well_order).
Qed.

(* Given a linear order on the set A and on the set B, 
  Sum A B is set on which their sum is defined *)
Inductive Sum (A B : Type) : Type :=
  | First : A -> Sum A B
  | Second : B -> Sum A B.

(* Given linear orders X and Y, define a relation sum_lt on the set Sum X.(set) Y.(set) *)
Definition sum_lt (X Y : LinearOrder) (x y : Sum X Y) : Prop :=
  match x, y with
  | First _ _ a, First _ _ b => a < b
  | Second _ _ a, Second _ _ b => a < b
  | First _ _ a, Second _ _ b => True
  | Second _ _ a, First _ _ b => False
  end.

(* Proving that the ordering on a sum of two linear orders is a linear order *)
Theorem sum_lt_transitive (X Y : LinearOrder) : transitive (sum_lt X Y).
Proof.
  intros a b c hab hbc. 
  destruct a as [s1|s2]. 
    destruct b as [r1|r2].
      destruct c.
        simpl. simpl in hab. simpl in hbc. exact (lt_transitive hab hbc).
        reflexivity.
      destruct c.
        simpl in hbc. contradiction.
        reflexivity.
    destruct b.
      destruct c.
        simpl in hab. contradiction.
        simpl in hab. contradiction.
      destruct c.
        simpl in hbc. contradiction.
        simpl in hab. simpl in hbc. simpl. exact (lt_transitive hab hbc).
 Qed.

Theorem sum_lt_irreflexive (X Y : LinearOrder) : irreflexive (sum_lt X Y).
Proof.
intros a haa.
destruct a.
  simpl in haa. apply (lt_irreflexive s). exact haa.
  simpl in haa. apply (lt_irreflexive s). exact haa.
Qed.

Theorem sum_lt_total (X Y : LinearOrder) : total (sum_lt X Y).
Proof.
intros a b.
destruct a. 
  destruct b.
    simpl. destruct (lt_total X s s0) as [c|d].
      left. exact c.
      right. destruct d. 
        left. rewrite H. reflexivity.
        right. exact H.
    simpl. left. trivial.
  destruct b.
    simpl. right. right. trivial.
    simpl. destruct (lt_total Y s s0) as [c|d].
      left. exact c.
      right. destruct d.
        left. rewrite H. reflexivity.
        right. exact H.
Qed.

(* Given linear orders X and Y, construct the linear order X + Y *)
Definition sum (X Y : LinearOrder) : LinearOrder :=
mkLinearOrder 
  (Sum X Y)
  (sum_lt X Y)
  (sum_lt_transitive X Y)
  (sum_lt_irreflexive X Y) 
  (sum_lt_total X Y).

(* Given a linear order X and property P, construct the suborder of X that satisfies P *)
Definition pred_order_relation (X : LinearOrder) (P : X -> Prop) : relation {x : X | P x} :=
fun a b : {x : X | P x} => proj1_sig a < proj1_sig b.

Theorem pred_order_transitive 
(X : LinearOrder) (P : X -> Prop) : transitive (pred_order_relation X P).
Proof.
unfold transitive. intros. unfold pred_order_relation in *.
exact (lt_transitive H H0).
Qed.

Theorem pred_order_irreflexive
(X : LinearOrder) (P : X -> Prop) : irreflexive (pred_order_relation X P).
Proof.
unfold irreflexive. intros. unfold pred_order_relation in *.
exact (lt_irreflexive (proj1_sig a)).
Qed.

Theorem pred_order_total
(X : LinearOrder) (P : X -> Prop) : total (pred_order_relation X P).
Proof.
unfold total. intros. unfold pred_order_relation in *.
destruct (lt_total _ (proj1_sig a) (proj1_sig b)).
- left. assumption.
- destruct H.
-- right. left. exact (same_proj1 _ _ _ _ H).
-- right. right. assumption.
Qed.

Definition pred_order 
(X : LinearOrder) (P : X -> Prop) : LinearOrder :=
{|
  set := {x : X | P x};
  lt := pred_order_relation X P;
  lt_transitive := pred_order_transitive X P;
  lt_irreflexive := pred_order_irreflexive X P;
  lt_total := pred_order_total X P;
|}.

Definition pred_order_embedding
{X : LinearOrder} {P : X -> Prop} (S : pred_order X P) : X :=
proj1_sig S.

Theorem pred_order_embedding_preserving
(X : LinearOrder) (P : X -> Prop) : 
forall a b : pred_order X P, a < b -> pred_order_embedding a < pred_order_embedding b.
Proof.
intros. unfold pred_order_embedding. unfold lt in H. simpl in H.
unfold pred_order_relation in H. assumption.
Qed.

(* The suborder of X satisfying a predicate P *)
Definition subset_pred_order (X : LinearOrder) (P : X -> Prop) : Suborder X :=
{|
  actual_order := pred_order X P;
  embedding := {|
    map := pred_order_embedding;
    order_preserving := pred_order_embedding_preserving X P;
  |}
|}.

Notation "{ x : A , P }" := (subset_pred_order A (fun x => P)) (x at level 99) : type_scope.

(* Defining the product of linear orders as indexed by a well order *)
Definition product_set {index : LinearOrder} (map : index -> LinearOrder) := 
forall (i : index), (map i).

Definition product_order 
{index : LinearOrder} (map : index -> LinearOrder) : 
relation (product_set map) := 
fun a b : product_set map =>
exists i : index, ((a i) < (b i)) /\ (forall j : index, j < i -> a j = b j).

Theorem product_order_transitive {index : LinearOrder} (map : index -> LinearOrder) :
transitive (product_order map).
Proof.
unfold transitive. intros. unfold product_order in *. 
destruct H. destruct H. destruct H0. destruct H0.
destruct (lt_total _ x x0).
- exists x. specialize (H2 x H3) as H4. split. 
-- rewrite H2 in H. assumption. assumption.
-- intros. specialize (H1 j H5) as H6.
assert (j < x0). { exact (lt_transitive H5 H3). }
specialize (H2 j H7) as H8.
rewrite <- H8. rewrite H6. reflexivity.
- exists x0. destruct H3.
-- rewrite H3 in H. split. exact (lt_transitive H H0).
intros. specialize (H2 j H4) as H5. rewrite <- H3 in H4. specialize (H1 j H4) as H6.
rewrite H6. rewrite H5. reflexivity.
-- specialize (H1 x0 H3) as H4. rewrite <- H4 in H0. split. assumption.
intros. specialize (H2 j H5). assert (j < x). { exact (lt_transitive H5 H3). }
specialize (H1 j H6). rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem product_order_irreflexive {index : LinearOrder} (map : index -> LinearOrder) :
irreflexive (product_order map).
Proof.
unfold irreflexive. intros. unfold product_order. unfold not. intros. destruct H.
destruct H. contradiction (@lt_irreflexive _ _ H).
Qed.

Theorem product_differences_has_min 
(index : LinearOrder) (map : index -> LinearOrder) (h : well_order index) 
: forall a b : product_set map, a <> b -> 
has_minimum (subset_pred_order index (fun i => a i <> b i)).
Proof.
intros. unfold not in H. unfold product_set in *. unfold well_order in h.
destruct (classic (exists i : index, a i <> b i)).
{ destruct H0. assert (c : (subset_pred_order index (fun i : index => a i <> b i))).
{ exact (exist (fun i : index => a i <> b i) x H0). }
exact (h (subset_pred_order index (fun i : index => a i <> b i)) c). }
{ specialize (not_ex_not_all index (fun i : index => a i = b i) H0) as H1.
simpl in H1.
extensionality in H1.
contradiction. }
Qed.

Theorem product_order_total {index : LinearOrder} 
(map : index -> LinearOrder) (h : well_order index) :
total (product_order map).
Proof.
unfold total. intros. destruct (classic (a=b)).
- right. left. assumption. 
- specialize (product_differences_has_min _ map h a b H) as H1.
unfold has_minimum in H1. destruct H1. specialize (proj2_sig x) as H1. simpl in H1.
destruct (lt_total _ (a (proj1_sig x)) (b (proj1_sig x))).
-- left. unfold product_order. exists (proj1_sig x). split. assumption.
intros. destruct (classic (a j = b j)). assumption.
unfold is_minimum in H0. unfold subset_pred_order in *. simpl in x. simpl in H0.
specialize (H0 (exist (fun i : index => a i <> b i) j H4)) as H5. 
unfold pred_order_relation in H5. simpl in H5.
destruct H5.
{ contradiction (lt_not_gt H3 H5). }
subst. simpl in *. contradiction (lt_irreflexive j).
-- destruct H2. { contradiction. }
{ right. right. unfold product_order. exists (proj1_sig x). split. assumption.
intros. destruct (classic (a j = b j)). symmetry. assumption.
unfold is_minimum in H0. unfold subset_pred_order in *. simpl in x. simpl in H0.
specialize (H0 (exist (fun i : index => a i <> b i) j H4)) as H5. 
unfold pred_order_relation in H5. simpl in H5.
destruct H5.
{ contradiction (lt_not_gt H3 H5). }
subst. simpl in *. contradiction (lt_irreflexive j). }
Qed.

Definition product (index : LinearOrder) (h : well_order index) (map : index -> LinearOrder) :=
{|
  set := product_set map;
  lt := product_order map;
  lt_transitive := product_order_transitive map;
  lt_irreflexive := product_order_irreflexive map;
  lt_total := product_order_total map h;
|}.

Inductive two_set :=
| Zero
| One.

Definition two_relation : relation two_set :=
fun a b : two_set => match a, b with
| Zero, One => True
| _, _ => False
end.

Theorem two_relation_transitive : transitive two_relation.
Proof.
unfold transitive. intros. destruct a,b,c; simpl; trivial.
Qed.

Theorem two_relation_irreflexive : irreflexive two_relation.
Proof.
unfold irreflexive. intros. 
destruct a; simpl; unfold not; intros; contradiction.
Qed.

Theorem two_relation_total : total two_relation.
Proof.
unfold total. intros. destruct a,b; firstorder.
Qed.

Definition two_embedding_map (a : two_set) : omega := 
match a with
| Zero => 0
| One => 1
end.

Definition two_order : LinearOrder :=
{|
  set := two_set;
  lt := two_relation;
  lt_transitive := two_relation_transitive;
  lt_irreflexive := two_relation_irreflexive;
  lt_total := two_relation_total;
|}.

Theorem two_embedding_order_preserving : 
forall a b : two_order, a < b -> two_embedding_map a < two_embedding_map b.
Proof.
intros. destruct a,b; simpl; firstorder.
Qed.

Definition two_embedding : Embedding two_order omega :=
mkEmbedding two_order omega two_embedding_map two_embedding_order_preserving.

Definition two : Suborder omega :=
{|
  actual_order := two_order;
  embedding := two_embedding;
|}.

Theorem two_well_order : well_order two.
Proof.
exact (suborder_omega_well_order two).
Qed.

Definition two_to_order_map (X Y : LinearOrder) (t : two) : LinearOrder :=
match t with
| Zero => X
| One => Y
end.

Notation "X * Y" := (product two two_well_order (two_to_order_map X Y)).

(*
(* Defining the produt of two linear orders as a special case *)
Definition two : Suborder omega := {n : omega, n < 2}.

Theorem zero_lt_two : (0 < 2)%nat.
Proof. specialize (le_n_S 0 1 (le_S 0 0 (le_n 0))) as H. assumption. Qed.
Theorem one_lt_two : (1 < 2)%nat.
Proof. unfold Peano.lt. exact (le_n 2). Qed.

Definition first_coord : two := exist _ 0 zero_lt_two.
Definition second_coord : two := exist _ 1 one_lt_two.

Theorem lt_two : forall a : nat, (a < 2)%nat -> a=0 \/ a=1.
Proof.
intros. destruct a.
- left. reflexivity.
- apply le_S_n in H. apply le_S_n in H. destruct a.
-- right. reflexivity.
-- contradiction (not_lt_zero a).
Qed. 

Theorem only_two_coords : forall a : two, a = first_coord \/ a = second_coord.
Proof.
intros. specialize (proj1_sig a) as H1. destruct (lt_two (proj1_sig a) (proj2_sig a)).
- left.
assert (proj1_sig first_coord = 0). { unfold first_coord. simpl. reflexivity. }
rewrite <- H0 in H. exact (same_proj1 _ _ _ _ H).
- right.
assert (proj1_sig second_coord = 1). { unfold second_coord. simpl. reflexivity. }
rewrite <- H0 in H. exact (same_proj1 _ _ _ _ H).
Qed.

Theorem two_well_order : well_order two.
Proof.
exact (suborder_omega_well_order two).
Qed.

Definition two_to_order_map (X Y : LinearOrder) (t : two) : LinearOrder :=
match t with
| exist _ 0 _ => X
| _ => Y
end.

Notation "X * Y" := (product two two_well_order (two_to_order_map X Y)).
*)

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

Structure ConvexEmbedding (X Y : LinearOrder) : Type := mkConvexEmbedding
{
convex_map :> Embedding X Y;
convexity : forall a c : X, forall y : Y, 
  ((convex_map a) < y /\ y < (convex_map c)) -> (exists b : X, convex_map b = y);
}.

Structure ConvexSuborder (Y : LinearOrder) : Type := mkConvexSuborder
{
source_order :> Suborder Y;
convex_embedding : forall a c : source_order, forall y : Y, 
  (embedding a) < y -> y < (embedding c) -> (exists b : source_order, embedding b = y);
}.

Arguments source_order {_}.

Definition convex_predicate (X : LinearOrder) (P : X -> Prop) :=
forall a b c : X, a < b -> b < c -> P a -> P c -> P b.

Theorem convex_predicate_convex (X : LinearOrder) (P : X -> Prop) (h : convex_predicate X P) :
forall a c : {x : X, P x}, forall y : X, (embedding a) < y -> y < (embedding c) ->
(exists b : {x : X, P x}, embedding b = y).
Proof.
intros. specialize (h (embedding a) y (embedding c)) as H1.
specialize (H1 H H0 (proj2_sig a) (proj2_sig c)) as b.
exists (exist _ y b). simpl. reflexivity.
Qed.

Definition convex_pred_order (X : LinearOrder) (P : X -> Prop)  (h : convex_predicate X P) : ConvexSuborder X :=
mkConvexSuborder X {x : X, P x} (convex_predicate_convex X P h).

Notation "{ x : A , P , h }" := 
(convex_pred_order A (fun x => P) h) (x at level 99) : type_scope.

Theorem pred_coord_convex (X Y : LinearOrder) (x : X) :
convex_predicate (X*Y) (fun j : (product two two_well_order (two_to_order_map X Y)) => j Zero = x).
Proof.
unfold convex_predicate. intros.
specialize (lt_transitive H H0) as H7. unfold lt in *. simpl in *. unfold product_order in *. simpl in *.
destruct H. destruct H. destruct H0. destruct H0. destruct H7. destruct H5.
destruct x0,x1,x2.
- (specialize (lt_transitive H H0) as H7). 
  rewrite H1 in H5. rewrite H2 in H5. contradiction (lt_irreflexive x).
- specialize (lt_transitive H H0) as H7. rewrite H1 in H7. rewrite H2 in H7.
  contradiction (lt_irreflexive x).
- rewrite H1 in H5. rewrite H2 in H5. contradiction (lt_irreflexive x).
- specialize (H4 Zero). simpl in H4. specialize (H4 I). rewrite H4. assumption.
- rewrite H1 in H5. rewrite H2 in H5. contradiction (lt_irreflexive x).
- specialize (H3 Zero). simpl in H3. specialize (H3 I). rewrite <- H3. assumption.
- rewrite H1 in H5. rewrite H2 in H5. contradiction (lt_irreflexive x).
- specialize (H4 Zero). simpl in H4. specialize (H4 I). rewrite H4. assumption.
Qed.

Definition prod_coord_suborder (X Y : LinearOrder) (x : X) : ConvexSuborder (X*Y) :=
{ j : X*Y , j Zero = x , pred_coord_convex X Y x}.

(* 
x ** Y is the convex suborder of X*Y with first coordinate x
xY = {(x, y)\in XY | y\in Y} 
*)
Notation "x ** Y" := (prod_coord_suborder _ Y x) (at level 100) : type_scope.


(* Formalizing the set R_f(x) = {y\in Y | yB \cap f(xA \cap I) \ne \emptyset}*)

(* 
For a fixed x, R_predicate is the predicate a y\in Y should satisfy to be in R_f(x) 
*)
Definition R_predicate {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)} 
(f : Isomorphism I J) (x : X) (y : Y) :=
exists (j : J) (j' : y ** B) (i : I) (i' : x ** A),
(embedding i) = (embedding i') /\ (embedding j) = (embedding j') /\ f i = j.


(*
Definition R_suborder {X Y A B : LinearOrder} (I : ConvexSuborder (X*A)) (J : ConvexSuborder (Y*B)) 
(f : Isomorphism (source_order (X*A) I) (source_order (Y*B) J)) : Suborder X :=
{ x : X, exists j : J, exists i : I, exists a : { j : X*A , j Zero = x }, 
(embedding i) = (embedding a) /\ f i = j }.

*)

Definition R_suborder {X Y A B : LinearOrder} (I : ConvexSuborder (X*A)) (J : ConvexSuborder (Y*B)) 
(f : Isomorphism I J) (x : X) : Suborder Y :=
{ y : Y, R_predicate f x y}.

(* Turn (x : X) and (y : Y) into pair (x,y) : X*Y *)
Definition prod_elem {X Y : LinearOrder} (x : X) (y: Y) : (product_set (two_to_order_map X Y)) :=
(fun a => match a with
| Zero => x
| One => y
end).

Theorem zero_prod_elem {X Y : LinearOrder} (x : X) (y : Y) : (prod_elem x y) Zero = x.
Proof. reflexivity. Qed.

(* Turn (x : X) and (y : Y) into the pair (x,y) : x**Y *)
Definition coord_prod_elem {X Y : LinearOrder} (x : X) (y: Y) : x**Y :=
exist 
(fun (a : (product_set (two_to_order_map X Y))) => a Zero = x) 
(prod_elem x y)
(zero_prod_elem x y).


Theorem R_suborder_convex {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) :
forall x : X, convex_predicate Y (R_predicate f x).
Proof.
unfold convex_predicate. intros. unfold R_predicate in *. 
destruct H1. destruct H1. destruct H1. destruct H1. destruct H1. destruct H3.
destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
assert (j' : b ** B). { exact (coord_prod_elem b (proj1_sig x1 One)). }
assert (proj1_sig x1 Zero < proj1_sig j' Zero) as G1.
{ rewrite (proj2_sig x1). rewrite (proj2_sig j'). assumption. }
assert (proj1_sig j' Zero < proj1_sig x5 Zero) as G2.
{ rewrite (proj2_sig j'). rewrite (proj2_sig x5). assumption. }
assert ((embedding x1) < (embedding j')). 
{
unfold lt. simpl. unfold pred_order_embedding. unfold product_order.
exists Zero. split. assumption.
intros. destruct j. contradiction. contradiction.
}
assert ((embedding j') < (embedding x5)).
{
unfold lt. simpl. unfold pred_order_embedding. unfold product_order.
exists Zero. split. assumption.
intros. destruct j. contradiction. contradiction.
}
rewrite <- H3 in H7. rewrite <- H5 in H8.
specialize (convex_embedding _ J x0 x4 (embedding j') H7 H8) as H9. destruct H9.
exists x8. exists j'.
specialize (surjective_map _ _ f x8) as H10. destruct H10.
exists x9.
assert (embedding x3 < embedding x9).
{
rewrite <- H1.
assert (x2 < x9).
{ apply (@order_preserving_backwards _ _ f).
rewrite H10. rewrite H4.
apply (@order_preserving_backwards _ _ embedding).
rewrite H9. assumption. }
apply (@order_preserving _ _ embedding). assumption.
}
assert (embedding x9 < embedding x7).
{
rewrite <- H2.
assert (x9 < x6).
{ apply (@order_preserving_backwards _ _ f).
rewrite H10. rewrite H6.
apply (@order_preserving_backwards _ _ embedding).
rewrite H9. assumption. }
apply (@order_preserving _ _ embedding). assumption.
}
specialize (convex_embedding _ (x**A) x3 x7 (embedding x9) H11 H12) as H13.
destruct H13. exists x10.
split. symmetry. assumption.
split. assumption. assumption.
Qed.

(* R_f(x) as a ConvexSuborder of Y *)
Definition R {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) (x : X) : ConvexSuborder Y :=
{y : Y, R_predicate f x y, R_suborder_convex f x}.













