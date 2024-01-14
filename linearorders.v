Require Import Classical.
Require Import Wf_nat.

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

Notation "x < y" := (lt _ x y).

Theorem lt_not_eq : forall X : LinearOrder, forall a b : X, a < b -> a <> b.
Proof.
intros. unfold not. intros. rewrite H0 in H. exact ((X.(lt_irreflexive) b) H).
Qed.

Theorem lt_not_gt : forall X : LinearOrder, forall a b : X, a < b -> ~(b < a).
Proof.
unfold not. intros. assert (a < a). { exact (X.(lt_transitive) a b a H H0). }
assert (~a<a). { exact (X.(lt_irreflexive) a). }
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
exact (X.(lt_transitive) c b a hcb hba).
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

Definition is_minimum {X : LinearOrder} (x : X) := forall y : X, x < y \/ x = y.
Definition has_minimum (X : LinearOrder) := exists x : X, is_minimum x.

Definition is_maximum {X : LinearOrder} (x : X) := forall y : X, y < x \/ y = x.
Definition has_maximum (X : LinearOrder) := exists x : X, is_maximum x.

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
- exact (lt_not_gt _ _ _ H H0).
- symmetry in H0. exact (lt_not_eq _ _ _ H H0).
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

Theorem order_preserving_backwards : 
forall (X Y : LinearOrder), 
forall (f : Embedding X Y),
forall (a b : X), f a < f b -> a < b.
Proof.
intros. assert (a < b \/ a = b \/ b < a).
{ exact (X.(lt_total) a b). }
destruct H0.
- assumption.
- destruct H0.
  -- assert (f a <> f b). { exact (lt_not_eq Y (f a) (f b) H). }
     assert (f a = f b). { rewrite H0. reflexivity. }
     contradiction.
  -- assert (f b < f a). { exact (order_preserving _ _ _ b a H0). }
     assert (~ f b < f a). { exact (lt_not_gt Y (f a) (f b) H). }
     contradiction.
Qed.

Theorem order_preserving_injective :
forall (X Y : LinearOrder), 
forall (f : Embedding X Y),
forall (a b : X), f a = f b -> a = b.
Proof.
intros. assert (a < b \/ a = b \/ b < a). { exact (X.(lt_total) a b). }
destruct H0.
- assert (f a < f b). { exact (order_preserving _ _ _ a b H0). }
  assert (f a <> f b). { exact (lt_not_eq _ _ _ H1). }
  contradiction.
- destruct H0.
  -- assumption.
  -- assert (f b < f a). { exact (order_preserving _ _ _ b a H0). }
     assert (f b <> f a). { exact (lt_not_eq _ _ _ H1). }
     assert (f a <> f b). { unfold not. intros. symmetry in H3. contradiction. }
     contradiction.
Qed.

Structure Suborder (Y : LinearOrder) : Type := mkSuborder
{
X :> LinearOrder;
embedding : Embedding X Y;
}.

Definition Image {X Y : Type} (f : X -> Y) := {y : Y | exists x : X, f x = y}.

Theorem same_proj1 : forall A : Type, forall P : A -> Prop,
forall (a b : {n : A | P n}), proj1_sig a = proj1_sig b -> a = b.
Proof.
intros. destruct a. destruct b. simpl in H.
subst. f_equal. apply proof_irrelevance.
Qed.

Definition well_order (X : LinearOrder) :=
forall A : Suborder X, (A -> has_minimum A).

Theorem zero_in_image_least : 
forall A : Suborder omega, (exists a : A, embedding omega A a = 0) -> has_minimum A.
Proof.
intros. destruct H. unfold has_minimum. exists x. unfold is_minimum. intros.
assert (embedding _ _ x < embedding _ _ y \/ embedding _ _ x = embedding _ _ y).
{ rewrite H. exact (zero_is_minimum (embedding _ _ y)). }
destruct H0.
- left. exact (order_preserving_backwards _ _ _ _ _ H0).
- right. exact (order_preserving_injective _ _ _ _ _ H0).
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
forall x : omega, x < embedding _ _ a -> forall b : A, embedding _ _ b <> x) ->
has_minimum A.
Proof. 
intros. destruct H. unfold has_minimum. exists x. unfold is_minimum.
intros. assert (x < y \/ x = y \/ y < x). { exact (A.(lt_total) x y). }
destruct H0.
- left. assumption.
- destruct H0.
* right. assumption.
* left. assert (embedding _ _ y < embedding _ _ x). 
{ exact (order_preserving  _ _ _ _ _ H0) . }
assert (embedding _ _ y <> embedding _ _ y). { exact (H (embedding _ _ y) H1 y). }
contradiction.
Qed.

Theorem omega_well_order : well_order omega.
Proof.
destruct (classic (well_order omega)).
- assumption.
- unfold well_order in H. apply not_all_ex_not in H.
destruct H.
assert (forall n : omega, ~(exists a : x, embedding omega x a = n)).
{ intros.
 induction n using (well_founded_induction lt_wf).
destruct (classic (exists a : x, embedding omega x a = n)).
{ destruct H1. 
assert (exists a : x, 
forall z : omega, z < embedding _ _ a -> forall b : x, embedding _ _ b <> z).
{ exists x0. intros. subst. specialize (H0 z H2) as H3. firstorder. }
specialize (prev_not_in_image_least _ H2) as H3.
assert (x -> has_minimum x). { intros. assumption. }
contradiction (H H4). }
assumption. }
assert (x -> has_minimum x). 
{ intros. specialize (H0 (embedding _ _ X0)) as H1. unfold not in H1.
assert (exists a : x, embedding omega x a = embedding omega x X0).
{ exists X0. reflexivity. }
contradiction. }
contradiction.
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
        simpl. simpl in hab. simpl in hbc. exact (X.(lt_transitive) s1 r1 s hab hbc).
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
        simpl in hab. simpl in hbc. simpl. exact (Y.(lt_transitive) s2 s s0 hab hbc).
 Qed.

Theorem sum_lt_irreflexive (X Y : LinearOrder) : irreflexive (sum_lt X Y).
Proof.
intros a haa.
destruct a.
  simpl in haa. apply (lt_irreflexive X s). exact haa.
  simpl in haa. apply (lt_irreflexive Y s). exact haa.
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




