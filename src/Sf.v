From LO Require Export FiniteCondensation.
From LO Require Export Rf.

Definition S_predicate {X Y A B : LinearOrder}
{I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)} 
(f : Isomorphism I J) (l : X / F) (q : (Y / F)) :=
exists x : (condensation_elem_to_interval l),
exists y : (condensation_elem_to_interval q),
exists y' : (R f (embedding x)), embedding y = embedding y'.

Definition S_suborder {X Y A B : LinearOrder}
{I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)} 
(f : Isomorphism I J) (l : X / F) : Suborder (Y / F) :=
  {q : Y / F, S_predicate f l q}. 

Theorem S_suborder_convex {X Y A B : LinearOrder}
{I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)} 
(f : Isomorphism I J) : 
forall l : X / F, convex_predicate (Y / F) (S_predicate f l).
Proof.
intros. unfold convex_predicate. intros. unfold S_predicate in *.
destruct H1. destruct H1. destruct H1.
destruct H2. destruct H2. destruct H2.
specialize (condensation_elem_interval_nonempty b) as q.
specialize (iso_inverse f) as H3. destruct H3. destruct H3.
specialize (proj2_sig x1) as H5. simpl in H5.
unfold R_predicate in H5. destruct H5. destruct H5.
destruct H5. destruct H5. destruct H5. destruct H6.
specialize (proj2_sig x4) as H8. simpl in H8.
unfold R_predicate in H8. destruct H8. destruct H8.
destruct H8. destruct H8. destruct H8. destruct H9.
assert (embedding x0 < embedding x3).
{ unfold embedding. simpl. unfold pred_order_embedding.
  specialize (lt_transitive H H0) as H11.
  unfold lt in H11. simpl in H11.
  unfold condensation_order in H11.
  exact (H11 (proj1_sig x0) (proj1_sig x3) (proj2_sig x0) (proj2_sig x3)). }
assert (embedding x0 < embedding q).
{ unfold embedding. simpl. unfold pred_order_embedding.
  unfold lt in H. simpl in H. unfold condensation_order in H.
  exact (H (proj1_sig x0) (proj1_sig q) (proj2_sig x0) (proj2_sig q)). }
assert (embedding q < embedding x3).
{ unfold embedding. simpl. unfold pred_order_embedding.
  unfold lt in H0. simpl in H0. unfold condensation_order in H0.
  exact (H0 (proj1_sig q) (proj1_sig x3) (proj2_sig q) (proj2_sig x3)). }
assert B.
{ exact ((proj1_sig x11) One). }
assert ((embedding q)** B).
{ exact (coord_prod_elem (embedding q) (X0)). }
assert (embedding x6 Zero = proj1_sig x1).
{ specialize (proj2_sig x7) as H14. simpl in H14. rewrite H6.
  simpl in *. rewrite <- H14. reflexivity. }
assert (embedding x10 Zero = proj1_sig x4) as H17.
{ specialize (proj2_sig x11) as H15. simpl in H15. rewrite H9.
  simpl in *. rewrite <- H15. reflexivity. }
assert (proj1_sig X1 Zero = embedding q).
{ specialize (proj2_sig X1) as H15. simpl in H15. simpl in *. assumption. }
assert (embedding x6 < embedding X1).
{ unfold lt. simpl. unfold product_order. unfold pred_order_embedding.
  exists Zero. simpl in H14. rewrite H14. simpl. split.
  { simpl in *. unfold pred_order_embedding in *. rewrite H15.
    rewrite <- H1. assumption. }
  { intros. destruct j.
    { subst. simpl in *. destruct H16. }
    { subst. simpl in *. destruct H16. } } }
assert (embedding X1 < embedding x10).
{ exists Zero. split.
  { rewrite H17. simpl in *. unfold pred_order_embedding in *.
    simpl in *. rewrite H15. rewrite <- H2. assumption. }
  { intros. destruct j.
    { destruct (lt_not_eq H18). reflexivity. }
    { destruct (H18). } } }
specialize (convex_embedding (Y*B) J x6 x10 (embedding X1) H16 H18) as H19.
destruct H19.
specialize (iso_inverse f) as H20. destruct H20. destruct H20.
set (X3 := x15 x14). set (r := embedding X3 Zero). simpl in r.
set (X4 := (elem_in_coord_suborder (embedding X3))).
assert (R_predicate f r (embedding q)).
{ unfold R_predicate. exists x14. exists X1. exists X3. exists X4.
  split.
  { reflexivity. }
  { split.
    { assumption. }
    { apply H21. } } }
set (q' := (exist _ (embedding q) H22) : R f r).
assert (embedding q' = embedding q).
{ unfold q'. reflexivity. }
assert (embedding x1 < embedding q').
{ rewrite <- H1. assumption. }
assert (embedding x <= r).
{ apply (R_preserves_order f (embedding x) r).
  exists x1. exists q'. assumption. }
assert (embedding q' < embedding x4).
{ rewrite <- H2. assumption. }
assert (r <= embedding x2).
{ apply (R_preserves_order f r (embedding x2)).
  exists q'. exists x4. assumption. }
destruct H25.
{ destruct H27.
  { specialize (convex_embedding 
                  X (condensation_elem_to_interval l) 
                  x x2 r H25 H27) as H28.
    destruct H28. exists x16. exists q. rewrite H28.
    exists q'. assumption. }
  { exists x2. exists q. rewrite <- H27. exists q'. assumption. } }
{ exists x. exists q. rewrite H25. exists q'. assumption. }
Qed.

Definition S {X Y A B : LinearOrder}
{I : ConvexSuborder (X*A)} {J : ConvexSuborder (Y*B)} 
(f : Isomorphism I J) (l : X / F) : ConvexSuborder (Y / F) :=
  {q : Y / F, S_predicate f l q, S_suborder_convex f l}. 
