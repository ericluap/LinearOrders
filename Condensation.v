From LO Require Export Convex.
From LO Require Export linearorders.
Require Import Classical.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

(* inspired by http://poleiro.info/posts/2019-12-25-quotients-in-coq.html
  and https://coq.discourse.group/t/naive-quotients-of-types/882 *)

Definition condensation_set (T : LinearOrder) (R : ConvexEquivRelation T) :=
  {f : T -> Prop | exists x : T, f = (actual_relation _ R) x}.


Theorem condensation_elem_valid {T : LinearOrder} (R : ConvexEquivRelation T) (x : T) :
exists x0 : T, (actual_relation _ R x) = (actual_relation _ R x0).
Proof.
exists x. reflexivity.
Qed.

Definition condensation_elem {T : LinearOrder} (R : ConvexEquivRelation T) (x : T)
: condensation_set T R :=
exist 
  (fun f => exists x : T, f = (actual_relation _ R) x)
  (actual_relation _ R x) (condensation_elem_valid R x).

Theorem condensation_elem_inj {T : LinearOrder} {R : ConvexEquivRelation T}
(x y : T) : condensation_elem R x = condensation_elem R y -> actual_relation _ R x y.
Proof.
intros.
assert (proj1_sig (condensation_elem R x) = proj1_sig (condensation_elem R y)).
{ rewrite H. reflexivity. }
simpl in H0.
assert (actual_relation _ R y y). apply eq_reflexive.
rewrite <- H0 in H1. assumption.
Qed.

Theorem related_means_eq_condensation {T : LinearOrder} {R : ConvexEquivRelation T}
{x y : T} : (actual_relation _ R x y) -> condensation_elem R x = condensation_elem R y.
Proof.
intros.
unfold condensation_elem.
assert (actual_relation _ R x = actual_relation _ R y).
{ apply functional_extensionality. intros.
  apply propositional_extensionality.
  split.
  - intros. assert (actual_relation _ R y x). exact (eq_symmetric _ R x y H).
    exact (eq_transitive _ R y x x0 H1 H0).
  - intros. exact (eq_transitive _ R x y x0 H H0). }
apply same_proj1. simpl. assumption.
Qed.

(* for any a,b : condensation_set, we say that a < b 
if for all x,y : T such that x \in a and y \in b, x < y*)
Definition condensation_order (T : LinearOrder) (R : ConvexEquivRelation T) :
relation (condensation_set T R) :=
fun a b => forall x y : T, proj1_sig a x -> proj1_sig b y -> x < y.

Theorem condensation_order_transitive (T : LinearOrder) (R : ConvexEquivRelation T) :
transitive (condensation_order T R).
Proof.
unfold transitive. unfold condensation_order. intros.
specialize (proj2_sig b) as H3. simpl in H3. destruct H3.
assert (proj1_sig b x0). { rewrite H3. exact (eq_reflexive _ R x0). }
specialize (H x x0 H1 H4) as H5.
specialize (H0 x0 y H4 H2) as H6.
exact (lt_transitive H5 H6).
Qed.

Theorem condensation_order_irreflexive (T : LinearOrder) (R : ConvexEquivRelation T) :
irreflexive (condensation_order T R).
Proof.
unfold irreflexive. unfold condensation_order. unfold not. intros.
specialize (proj2_sig a) as H1. simpl in H1. destruct H1.
assert (proj1_sig a x). { rewrite H0. exact (eq_reflexive _ R x). }
exact (lt_irreflexive x (H x x H1 H1)).
Qed.

Theorem condensation_order_total (T : LinearOrder) (R : ConvexEquivRelation T) :
total (condensation_order T R).
Proof.
unfold total. unfold condensation_order. intros.
specialize (proj2_sig a) as H0. specialize (proj2_sig b) as H1.
simpl in *. destruct H0, H1.
destruct (classic (actual_relation _ R x x0)).
- right. left. specialize (related_means_eq_condensation H1) as H2.
assert (a = condensation_elem R x). apply same_proj1. simpl. assumption.
assert (b = condensation_elem R x0). apply same_proj1. simpl. assumption.
rewrite H3. rewrite H4. assumption.
- destruct (lt_total _ x x0).
-- left. intros. destruct (lt_total _ x1 y).
{ assumption. }
{ destruct H5.
{ rewrite H in H3. rewrite H0 in H4. rewrite H5 in H3.
contradiction (eq_transitive T R _ _ _ H3 (eq_symmetric T R _ _ H4)). }
rewrite H in H3. rewrite H0 in H4.
destruct (lt_total _ x y).
- specialize (eq_convex T R x y x1 H6 H5 H3) as H7.
apply eq_symmetric in H4. contradiction (eq_transitive T R _ _ _ H7 H4).
- destruct H6.
-- rewrite <- H6 in H4. apply eq_symmetric in H4. contradiction.
-- apply eq_symmetric in H4.
  specialize (eq_convex T R y x x0 H6 H2 H4) as H7.
  apply eq_symmetric in H7.
  contradiction (eq_transitive T R _ _ _ H7 H4). }
-- destruct H2.
{ right. left. subst. apply same_proj1. rewrite H. rewrite H0. reflexivity. }
{ right. right. intros. destruct (lt_total _ x1 y).
{ assumption. }
{ destruct H5.
{ rewrite H in H4. rewrite H0 in H3. rewrite H5 in H3.
contradiction (eq_transitive T R _ _ _ H4 (eq_symmetric T R _ _ H3)). }
rewrite H in H4. rewrite H0 in H3.
destruct (lt_total _ x y).
- specialize (lt_transitive H6 H5) as H7.
  specialize (eq_convex T R x0 x x1 H2 H7 H3) as H8. apply eq_symmetric in H8.
  contradiction.
- destruct H6.
-- rewrite <- H6 in H5.
  specialize (eq_convex T R x0 x x1 H2 H5 H3) as H8. apply eq_symmetric in H8.
  contradiction.
-- destruct (lt_total _ x0 y).
{ specialize (eq_convex T R x0 y x1 H7 H5 H3) as H8. apply eq_symmetric in H8.
  contradiction (eq_transitive T R _ _ _ H4 H8). }
{ destruct H7. rewrite <- H7 in H4. contradiction. apply eq_symmetric in H4.
specialize (eq_convex T R y x0 x H7 H2 H4) as H8. apply eq_symmetric in H4.
contradiction (eq_transitive T R _ _ _ H4 H8). } } }
Qed.

Definition CondensationOrder (T : LinearOrder) (R : ConvexEquivRelation T) :=
mkLinearOrder 
  (condensation_set T R)
  (condensation_order T R)
  (condensation_order_transitive T R)
  (condensation_order_irreflexive T R)
  (condensation_order_total T R).

Notation "X / P" := (CondensationOrder X P).

Theorem condensation_elem_convex {T : LinearOrder} {P : ConvexEquivRelation T}
(l : T/P) : convex_predicate T (proj1_sig l).
Proof.
unfold convex_predicate. intros.
specialize (proj2_sig l) as H3. simpl in H3. destruct H3.
rewrite H3 in H1. rewrite H3 in H2. apply eq_symmetric in H1.
specialize (eq_transitive T P _ _ _ H1 H2) as H4.
specialize (eq_convex T P a b c H H0 H4) as H5.
apply eq_symmetric in H1.
specialize (eq_transitive T P _ _ _ H1 H5) as H6.
rewrite <- H3 in H6. assumption.
Qed.

Definition condensation_elem_to_interval {T : LinearOrder} {P : ConvexEquivRelation T}
(l : T/P) : ConvexSuborder T := {t : T, (proj1_sig l t), condensation_elem_convex l}.