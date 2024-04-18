From LO Require Export Suborder.
From LO Require Export Reverse.
Require Import Classical.
Require Import Wf_nat.

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

(* omega_star is the natural numbers with the reverse ordering *)
Definition omega_star : LinearOrder := reverse omega.

(* Proving that properties about minimums and maximums for omega *)
Theorem zero_is_minimum : is_minimum (0 : omega).
Proof.
unfold is_minimum. intros. induction y.
- right. trivial.
- destruct IHy.
  --  apply le_S in H. left. assumption.
  --  left. assert (Peano.le 0 y). rewrite H. trivial. apply le_n_S in H0. assumption.
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