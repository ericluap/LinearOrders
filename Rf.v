From LO Require Export Convex.
From LO Require Export Isomorphism.

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
