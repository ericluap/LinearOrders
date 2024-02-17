From LO Require Export Convex.
From LO Require Export Isomorphism.
From LO Require Export Finiteness.
Require Import FunctionalExtensionality.

(* Formalizing the set R_f(x) = {y\in Y | yB \cap f(xA \cap I) \ne \emptyset}*)

(* 
For a fixed x, R_predicate is the predicate a y\in Y should satisfy to be in R_f(x) 
*)
Definition R_predicate {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)} 
(f : Isomorphism I J) (x : X) (y : Y) :=
exists (j : J) (j' : y ** B) (i : I) (i' : x ** A),
(embedding i) = (embedding i') /\ (embedding j) = (embedding j') /\ f i = j.

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

Theorem create_R_for_J {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) (j : J) :
exists x : X, exists y : R f x, embedding y = (embedding j Zero).
Proof.
set (y := embedding j Zero). simpl in y.
specialize (iso_inverse f) as H. destruct H as [fi]. destruct H.
set (i := fi j).
set (x := embedding i Zero). simpl in x.
set (b := embedding j One). simpl in b.
set (j' := coord_prod_elem y b).
assert (embedding j' One = embedding j One).
{ reflexivity. }
assert (embedding j' Zero = embedding j Zero).
{ reflexivity. }
assert (forall s : two_set, embedding j' s = embedding j s).
{ intros. destruct s; assumption. }
assert (embedding j' = embedding j).
{ apply functional_extensionality_dep. assumption. }
set (a := embedding i One). simpl in a.
set (i' := coord_prod_elem x a).
assert (R_predicate f x y).
{ unfold R_predicate. exists j. exists j'. exists i. exists i'.
  split.
  { simpl. apply functional_extensionality_dep. intros. unfold prod_elem.
    destruct x0; reflexivity. }
  { split.
    { symmetry. assumption. }
    { exact (H0 j). } } }
set (y' := exist _ y H5).
exists x. exists y'. reflexivity.
Qed.

Theorem R_preserves_order {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) (x1 x2 : X) (x : R f x1) (x0 : R f x2):
embedding x < embedding x0 -> x1 <= x2.
Proof.
intros. unfold R in *.
specialize (proj2_sig x) as H1. simpl in H1.
specialize (proj2_sig x0) as H2. simpl in H2.
unfold R_predicate in H1, H2.
destruct H1. destruct H0. destruct H0. destruct H0. destruct H0.
destruct H1. destruct H2. destruct H2. destruct H2. destruct H2.
destruct H2. destruct H4.
specialize (iso_inverse f) as H6. destruct H6. destruct H6.
assert (embedding x4 < embedding x8).
{ unfold lt. simpl. unfold product_order. exists Zero. split.
  { specialize (proj2_sig x4) as H8. simpl in H8.
    specialize (proj2_sig x8) as H9. simpl in H9.
    assert (pred_order_embedding x4 Zero = proj1_sig x).
    { unfold pred_order_embedding. assumption. }
    simpl in H10. rewrite H10.
    assert (pred_order_embedding x8 Zero = proj1_sig x0).
    { unfold pred_order_embedding. assumption. }
    simpl in H11. rewrite H11. apply H. }
  { intros. destruct j; destruct H8. } }
rewrite <- H1 in H8. rewrite <- H4 in H8.
specialize (order_preserving_backwards H8) as H9.
assert (x11 x3 < x11 x7).
{ exact (order_preserving H9). }
rewrite <- H3 in H10. rewrite <- H5 in H10.
rewrite (H6 x5) in H10. rewrite (H6 x9) in H10.
specialize (order_preserving H10 : (embedding x5 < embedding x9)) as H11.
rewrite H0 in H11. rewrite H2 in H11.
unfold lt in H11. simpl in H11. unfold product_order in H11.
destruct H11. destruct H11.
specialize (proj2_sig x6) as H13. simpl in H13.
specialize (proj2_sig x10) as H14. simpl in H14.
unfold pred_order_embedding in H11. simpl in H13. simpl in H11.
destruct x12.
{ rewrite H13 in H11. simpl in H14. rewrite H14 in H11. left. assumption. }
{ specialize (H12 Zero) as H15. simpl in H15.
  assert (True). { trivial. } specialize (H15 H16).
  unfold pred_order_embedding in H15. simpl in H13, H14. simpl in H15.
  rewrite H13 in H15. rewrite H14 in H15. right. assumption. }
Qed.

Theorem create_R_inbetween {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) (x1 x2 : X) (y : Y) (y1 : R f x1) (y2 : R f x2)
(p1 : embedding y1 < y) (p2 : y < embedding y2) :
exists x : X, (exists y' : R f x, embedding y' = y) /\ x1 <= x /\ x <= x2.
Proof.
specialize (proj2_sig y1) as H1. specialize (proj2_sig y2) as H2.
simpl in H1, H2. destruct H1, H2. destruct H, H0. destruct H, H0.
destruct H, H0. destruct H, H0. destruct H1, H2.
set (b := (proj1_sig x4 One)). simpl in b.
set (yb := coord_prod_elem y b).
assert (embedding x < embedding yb).
{ unfold lt. simpl. unfold product_order. exists Zero.
  simpl in H1. rewrite H1. simpl. specialize (proj2_sig x3) as H5.
  simpl in H5. unfold pred_order_embedding. split.
  { simpl. rewrite H5. assumption. }
  { intros. unfold two_relation in H6. destruct j; destruct H6. } }
assert (embedding yb < embedding x0).
{ unfold lt. simpl. unfold product_order. exists Zero.
  simpl in H2. rewrite H2. simpl. specialize (proj2_sig x4) as H6.
  simpl in H6. unfold pred_order_embedding. split.
  { simpl. rewrite H6. assumption. }
  { intros. unfold two_relation in H7. destruct j; destruct H7. } }
specialize (convex_embedding (Y*B) J x x0 (embedding yb) H5 H6) as H7.
destruct H7. specialize (create_R_for_J f x9) as H8.
destruct H8. destruct H8. exists x10. split. 
{ exists x11. rewrite H8. rewrite H7. reflexivity. }
{ split.
  { assert (embedding y1 < embedding x11).
    { rewrite H8. rewrite H7. assumption. }
    exact (R_preserves_order f x1 x10 y1 x11 H9). }
  { assert (embedding x11 < embedding y2).
    { rewrite H8. rewrite H7. assumption. }
    exact (R_preserves_order f x10 x2 x11 y2 H9). } }
Qed.

Definition R_interval_predicate {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) (E : ConvexSuborder X) (y : Y) :=
  exists (e : E) (y' : R f (embedding e)), embedding y' = y.

Definition R_interval_suborder {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) (E : ConvexSuborder X) : Suborder Y :=
  {y : Y, R_interval_predicate f E y}.

Theorem R_interval_predicate_convex {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) :
forall E : ConvexSuborder X, convex_predicate Y (R_interval_predicate f E).
Proof.
intros. unfold convex_predicate. intros.
unfold R_interval_predicate in *. destruct H1. destruct H1. 
destruct H2. destruct H2.
assert (embedding x0 < b). { rewrite H1. assumption. }
assert (b < embedding x2). { rewrite H2. assumption. }
specialize (create_R_inbetween f (embedding x) (embedding x1) b x0 x2 H3 H4) as H5.
destruct H5. destruct H5. destruct H5. destruct H6.
destruct H6.
{ destruct H7.
  { specialize (convex_embedding X E x x1 x3 H6 H7) as H8.
    destruct H8. exists x5. subst. exists x4. reflexivity. }
  { exists x1. rewrite <- H7. exists x4. assumption. } }
{ exists x. rewrite H6. exists x4. assumption. }
Qed.

Definition R_interval {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) (E : ConvexSuborder X) : ConvexSuborder Y :=
  {y : Y, R_interval_predicate f E y, R_interval_predicate_convex f E}.

(*
Theorem R_finite_to_infinite {X Y A B : LinearOrder} {I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)}
(f : Isomorphism I J) :
forall (E : ConvexSuborder X), is_finite E -> is_infinite (R_interval f E) ->
exists x : X, is_infinite (R f x).
Proof.
intros.*)

