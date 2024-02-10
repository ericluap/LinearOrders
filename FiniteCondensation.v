From LO Require Export Condensation.
From LO Require Export Finiteness.
Require Import Classical.
Require Import Description.
Require Import Arith.
Require Import Lia.

Definition endpoint_predicate {X : LinearOrder} (x y z : X) :=
  (x < z /\ z < y).

Theorem endpoint_predicate_convex {X : LinearOrder} (x y : X) 
: convex_predicate X (endpoint_predicate x y).
Proof.
unfold convex_predicate. unfold endpoint_predicate. intros.
destruct H1. destruct H2. split.
exact (lt_transitive H1 H).
exact (lt_transitive H0 H4).
Qed.

Definition interval_with_endpoints {X : LinearOrder} (x y : X) : ConvexSuborder X :=
{z : X, endpoint_predicate x y z, endpoint_predicate_convex x y}.

Notation "[( x , y )]" := (interval_with_endpoints x y).

Definition elem_of_endpoint_interval {X : LinearOrder} {x y a : X}
(H1 : x < a) (H2 : a < y) : [(x,y)] :=
exist _ a (conj H1 H2).

Definition finite_relation (X : LinearOrder) : relation X :=
  fun x y : X => is_finite [(x,y)] /\ is_finite [(y,x)].

Theorem finite_relation_symmetric (X : LinearOrder) : symmetric (finite_relation X).
Proof.
unfold symmetric. unfold finite_relation. unfold is_finite. intros.
destruct H. split; assumption.
Qed.

Theorem zero_lt_one : (0 : omega) < (1 : omega).
Proof. unfold lt. simpl. unfold Peano.lt. reflexivity. Qed.

Definition zero_in_lt_one : {m : omega, m < 1} :=
  (exist (fun x => x < (1 : omega)) 0 zero_lt_one).

Theorem finite_relation_reflexive (X : LinearOrder) : reflexive (finite_relation X).
Proof.
unfold reflexive. unfold finite_relation. unfold is_finite. intros.
assert 
  (forall c d : [(a,a)],
     c < d -> 
    (fun x : [(a,a)] => zero_in_lt_one) c < 
    (fun x : [(a,a)] => zero_in_lt_one) d).
{ intros. specialize (proj2_sig c) as H1. simpl in H1. destruct H1. 
contradiction (lt_irreflexive _ (lt_transitive H0 H1)). }
split;
exists 1;
exists (mkEmbedding [(a,a)] {m:omega,m<1} (fun x : [(a,a)] => zero_in_lt_one) H);
trivial.
Qed. 


Theorem split_finite_interval {X : LinearOrder} (a b c : X)  :
forall y : [(a,c)], 
  (b = embedding y) \/ 
  (exists z : [(a,b)], embedding z = proj1_sig y) \/
  (exists z : [(b,c)], embedding z = proj1_sig y).
Proof.
 intros. specialize (proj2_sig y) as H1. simpl in H1.
  unfold endpoint_predicate in H1. destruct H1.
  destruct (lt_total X b (proj1_sig y)).
  - right. right. exists (elem_of_endpoint_interval H1 H0).
    reflexivity.
  - destruct H1.
  -- left. rewrite H1. reflexivity.
  -- right. left. exists (elem_of_endpoint_interval H H1).
     reflexivity.
Qed.

Definition finite_transitive_map_property {X : LinearOrder} 
(a b c : X) (n1 n2 : omega) 
(f1 : [(a,b)] -> {x : omega, x < n1})
(f2 : [(b,c)] -> {x : omega, x < n2}) (y : [(a,c)]) (n : omega) :=
(n < n1 + 1 + n2 + 1) /\
(proj1_sig y < b -> 
  exists z : [(a,b)], proj1_sig z = proj1_sig y /\ proj1_sig (f1 z) = n) /\
(proj1_sig  y = b -> n = n1) /\
(lt b (proj1_sig y) -> 
  exists z : [(b,c)], proj1_sig z = proj1_sig y /\ proj1_sig (f2 z) + 1 + n1 = n)
.

Definition extract_lt_proof {X : LinearOrder} {a b c : X} {n1 n2 : omega}
{f1 : [(a,b)] -> {x : omega, x < n1}}
{f2 : [(b,c)] -> {x : omega, x < n2}} {y : [(a,c)]} {n : omega}
(p : finite_transitive_map_property a b c n1 n2 f1 f2 y n) :=
match p with
| conj a _ => a
end.

Definition finite_transitive_map_property_unique {X : LinearOrder} 
(a b c : X) (n1 n2 : omega) 
(f1 : [(a,b)] -> {x : omega, x < n1})
(f2 : [(b,c)] -> {x : omega, x < n2}) :=
forall y : [(a,c)], exists! n : omega,
(proj1_sig y < b -> 
  exists z : [(a,b)], proj1_sig z = proj1_sig y /\ proj1_sig (f1 z) = n) /\
(proj1_sig  y = b -> n = n1) /\
(lt b (proj1_sig y) -> 
  exists z : [(b,c)], proj1_sig z = proj1_sig y /\ proj1_sig (f2 z) + 1 + n1 = n)
.

Theorem wrong_order_implies_all {X : LinearOrder}
{a b : X} (H : a < b) (z : [(b,a)]) {P : Type} : P.
Proof.
specialize (proj2_sig z) as H1. simpl in H1.
unfold endpoint_predicate in H1. destruct H1.
specialize (lt_transitive H0 H1) as H2.
destruct (lt_not_gt H2 H).
Qed.

Theorem finite_if_wrong_order {X : LinearOrder}
{a b : X} (H : a < b) : is_finite [(b,a)].
Proof.
unfold is_finite. exists 1.
assert (forall y : [(b,a)], {n : omega, n < 1}).
{ intros. exact (wrong_order_implies_all H y). }
assert (forall x y : [(b,a)], x < y -> X0 x < X0 y).
{ intros. exact (wrong_order_implies_all H y). }
exists {|
  map := fun y : [(b,a)] => X0 y;
  order_preserving := H0;
|}. trivial.
Qed.

Theorem finite_relation_transitive_case {X : LinearOrder}
{a b c : X} (H1 : a < b) (H2 : b < c) 
(p3 : is_finite [(a,b)]) (p4 : is_finite [(b,c)]) : 
is_finite [(a,c)].
Proof.
unfold is_finite in *.
destruct p3. destruct H.
destruct p4 as [x2 H0]. destruct H0 as [x3].
set (x1 := True).
set (x4 := True).
set (x5 := True).
set (x6 := True).
{ exists (x+1+x2+1).
  assert (finite_transitive_map_property_unique a b c x x2 x0 x3). 
  { unfold finite_transitive_map_property_unique. intros.
    assert (a < proj1_sig y).
    { specialize (proj2_sig y) as H3. simpl in H3. destruct H3. assumption. }
    assert (proj1_sig y < c) as H11.
    { specialize (proj2_sig y) as H4. simpl in H4. destruct H4. assumption. }
    destruct (lt_total _ (proj1_sig y) b).
    { exists (proj1_sig (x0 (elem_of_endpoint_interval H3 H4))).
      unfold unique.
      split. 
        { split. 
          { intros. exists (elem_of_endpoint_interval H3 H4).
            split; reflexivity. }
          { split.
            { intros. destruct (lt_not_eq H4 H5). }
            { intros. destruct (lt_irreflexive b (lt_transitive H5 H4)). } } }
        { intros. destruct H5. specialize (H5 H4) as H7. destruct H7.
          destruct H7. assert (x7 = (elem_of_endpoint_interval H3 H4)).
          { apply same_proj1. simpl. assumption. }
          rewrite <- H9. assumption. } }
    { destruct H4.
      { exists x. unfold unique. split.
        { split.
          { intros. destruct (lt_not_eq H5 H4). }
          { split.
            { intros. reflexivity. }
            { intros. symmetry in H4. destruct (lt_not_eq H5 H4). } } }
        { intros. destruct H5. destruct H6. symmetry. apply H6. assumption. } }
      { exists (proj1_sig (x3 (elem_of_endpoint_interval H4 H11)) + 1 + x).
        unfold unique. split.
        { split.
          { intros. destruct (lt_irreflexive b (lt_transitive H4 H5)). }
          { split.
            { intros. symmetry in H5. destruct (lt_not_eq H4 H5). }
            { intros. exists (elem_of_endpoint_interval H4 H11). split; reflexivity. } } }
        { intros. destruct H5. destruct H6. specialize (H7 H4) as H8. destruct H8. destruct H8.
          assert (elem_of_endpoint_interval H4 H11 = x7).
          { apply same_proj1. simpl. symmetry. assumption. }
          rewrite H10. assumption. } } } }
    { assert (forall y : [(a,c)], {n : omega, finite_transitive_map_property a b c x x2 x0 x3 y n}).
      { intros. specialize (H3 y) as H4. apply constructive_definite_description.
        destruct H4. destruct H4. assert (x7 < x + 1 + x2 + 1).
        { assert (x < x+1+x2+1) as H12. 
            { simpl. unfold Peano.lt.
              specialize (PeanoNat.Nat.le_add_r (S x) (x2 + 1)) as H12.
              rewrite (PeanoNat.Nat.add_comm x 1).
              rewrite <- (PeanoNat.Nat.add_assoc (1 + x) x2 1).
              simpl in *. assumption. }
          destruct (lt_total _ (proj1_sig y) b).
          { destruct H4. specialize (H4 H6) as H8. destruct H8. destruct H8.
            specialize (proj2_sig (x0 x8)) as H10. simpl in H10.
            assert (x7 < x). { rewrite <- H9. assumption. }
            exact (lt_transitive H11 H12). }
          { destruct H6.
            { destruct H4. destruct H7. specialize (H7 H6) as H9. rewrite H9. assumption. }
            { destruct H4. destruct H7. specialize (H8 H6) as H9. destruct H9. destruct H9.
              specialize (proj2_sig (x3 x8)) as H11. simpl in H11.
              specialize (Nat.add_lt_mono_r (proj1_sig (x3 x8)) x2 (1 + x + 1)) as H13.
              destruct H13. specialize (H13 H11) as H15.
              assert (proj1_sig (x3 x8) + ((1+x)+1) = (proj1_sig (x3 x8) + 1 + x) + 1).
              { rewrite PeanoNat.Nat.add_assoc. rewrite PeanoNat.Nat.add_assoc. reflexivity. }
              rewrite H16 in H15. rewrite H10 in H15.
              assert (x2+((1+x)+1) = (x+1)+x2+1).
              { rewrite PeanoNat.Nat.add_comm. rewrite <- PeanoNat.Nat.add_assoc.
                rewrite <- PeanoNat.Nat.add_assoc. rewrite PeanoNat.Nat.add_comm.
                rewrite PeanoNat.Nat.add_assoc. reflexivity. }
              rewrite H17 in H15.
              assert (x7 < x7 + 1). 
              { simpl. unfold Peano.lt. rewrite PeanoNat.Nat.add_comm. reflexivity. }
              exact (lt_transitive H18 H15). } } }
       exists x7. unfold unique. split.
       { unfold finite_transitive_map_property. split.
         { assumption. }
         { split.
           { intros. destruct H4. exact (H4 H7). }
           { split.
             { intros. destruct H4. destruct H8. exact (H8 H7). }
             { intros. destruct H4. destruct H8. exact (H9 H7). } } } }
       { intros. unfold finite_transitive_map_property in H7. destruct H7.
          exact (H5 x' H8). } }
  { assert (forall z w : [(a,c)], z < w -> proj1_sig (X0 z) < proj1_sig (X0 w)).
    { intros. specialize (proj2_sig (X0 z)) as H6. simpl in H6.
      specialize (proj2_sig (X0 w)) as H7. simpl in H7. unfold finite_transitive_map_property in *.
      destruct H6. destruct H6. destruct H8. destruct H7. destruct H10. destruct H11.
      destruct (lt_total _ (proj1_sig z) b).
      { destruct (lt_total _ (proj1_sig w) b).
        { specialize (H6 H13) as H15. destruct H15. destruct H15.
          specialize (H10 H14) as H17. destruct H17. destruct H17.
          assert ((proj1_sig z) < (proj1_sig w)).
          { unfold lt in H4. simpl in H4. unfold pred_order_relation in H4.
            assumption. }
          assert (proj1_sig x7 < proj1_sig x8).
          { rewrite H15. rewrite H17. assumption. }
          assert (x7 < x8).
          { simpl. unfold pred_order_relation. assumption. }
          assert ((x0 x7) < (x0 x8)).
          { exact (order_preserving H21). }
          assert (proj1_sig (x0 x7) < proj1_sig (x0 x8)).
          { unfold lt in H22. simpl in H22. assumption. }
          simpl in *. rewrite <- H16. rewrite <- H18. assumption. }
        { destruct H14.
          { specialize (H6 H13) as H15. destruct H15. destruct H15.
            specialize (H11 H14) as H17.
            specialize (proj2_sig (x0 x7)) as H18. simpl in H18.
            rewrite <- H17 in H18. simpl in *. rewrite H16 in H18.
            assumption. }
          { specialize (H6 H13) as H15. destruct H15. destruct H15.
            specialize (H12 H14) as H17. destruct H17. destruct H17.
            specialize (proj2_sig (x0 x7)) as H19. simpl in H19.
            assert (proj1_sig (x0 x7) < x). { simpl. assumption. }
            assert (x < (proj1_sig (x3 x8))+1+x).
            { simpl. lia. }
            specialize (lt_transitive H20 H21) as H22.
            simpl in *. rewrite H16 in H22. rewrite H18 in H22. assumption. } } }
      { destruct (lt_total _ (proj1_sig w) b).
        { destruct H13; simpl in H4; unfold pred_order_relation in H4.
          { rewrite <- H13 in H14. contradiction (lt_not_gt H14 H4). }
          { contradiction (lt_not_gt (lt_transitive H14 H13) H4). } }
        { simpl in H4; unfold pred_order_relation in H4.
          destruct H13.
          { destruct H14.
            { rewrite <- H13 in H14. symmetry in H14. destruct (lt_not_eq H4 H14). }
            { specialize (H12 H14) as H15. destruct H15. destruct H15.
              specialize (H8 H13) as H17.
              specialize (proj2_sig (x3 x7)) as H18. simpl in H18.
              assert (x < ((proj1_sig (x3 x7))+1+x)). { simpl. lia. }
              simpl in *. rewrite H17. rewrite <- H16. assumption. } }
        { destruct H14.
          { rewrite <- H14 in H13. destruct (lt_not_gt H13 H4). }
          { specialize (H12 H14) as H15. destruct H15. destruct H15.
            specialize (H9 H13) as H17. destruct H17. destruct H17.
            rewrite <- H15 in H4. rewrite <- H17 in H4.
            assert (x3 x8 < x3 x7). { apply order_preserving. assumption. }
            simpl in H19.
            assert (Peano.lt (((proj1_sig (x3 x8)) + 1) + x) (((proj1_sig (x3 x7)) + 1) + x)).
            { simpl in *. lia. }
            simpl in *. rewrite H18 in H20. rewrite H16 in H20. assumption. } } } } }          
    set (X1 := (fun (y : [(a,c)]) => 
      create_elem_of_pred_order 
        (fun a : omega => a < x+1+x2+1)
        (proj1_sig (X0 y)) 
        (extract_lt_proof (proj2_sig (X0 y))))).
    assert (forall z w : [(a,c)], z < w -> (X1 z < X1 w)).
    { intros. unfold X1. simpl. exact (H4 z w H5). }
    exists {|
      map := X1;
      order_preserving := H5;
    |}. trivial. } } }
Qed.

Theorem subinterval_is_finite {X : LinearOrder}
{a b c d : X} (p : is_finite [(a,b)]) (p2 : a < c \/ a = c)
(p3 : d < b \/ d = b) : is_finite [(c,d)].
Proof.
unfold is_finite in *. destruct p. destruct H.
exists x. destruct p2.
{ destruct p3.
  { set (f := fun y : [(c,d)] => 
      match (proj2_sig y) with
      | conj cLty yLtd =>
        elem_of_endpoint_interval (lt_transitive H0 cLty) (lt_transitive yLtd H1)
      end).
    assert (forall z w : [(c,d)], z < w -> f z < f w).
    { intros.
      unfold f. 
      destruct (proj2_sig z). destruct (proj2_sig w). simpl.
      unfold pred_order_relation. simpl. unfold lt in H2. simpl in H2.
      unfold pred_order_relation in H2. assumption. }
    set (f_emb := {| map := f; order_preserving := H2; |}).
    exists (embedding_embedding f_emb x0). trivial. }
  { set (f := fun y : [(c,d)] => 
      match (proj2_sig y) with
      | conj cLty yLtd =>
        elem_of_endpoint_interval (lt_transitive H0 cLty) yLtd
      end). 
    subst.
    assert (forall z w : [(c, b)], z < w -> f z < f w).
    { intros. unfold f. destruct (proj2_sig z). destruct (proj2_sig w).
    simpl. unfold pred_order_relation.
    simpl. exact H1. }
    set (f_emb := {| map := f; order_preserving := H1; |}).
    exists (embedding_embedding f_emb x0). trivial. } }
{ destruct p3.
  { set (f := fun y : [(c,d)] => 
      match (proj2_sig y) with
      | conj cLty yLtd =>
        elem_of_endpoint_interval cLty (lt_transitive yLtd H1)
      end). 
    subst.
    assert (forall z w : [(c, d)], z < w -> f z < f w).
    { intros. unfold f. destruct (proj2_sig z). destruct (proj2_sig w).
    simpl. unfold pred_order_relation.
    simpl. exact H0. }
    set (f_emb := {| map := f; order_preserving := H0; |}).
    exists (embedding_embedding f_emb x0). trivial. }
  { subst. exists x0. trivial. } }
Qed.

Theorem finite_relation_transitive (X : LinearOrder) : transitive (finite_relation X).
Proof.
unfold transitive. unfold finite_relation.
intros. destruct H. destruct H0.
destruct (lt_total _ a b). 
{ destruct (lt_total _ b c). 
  { split. 
    { exact (finite_relation_transitive_case H3 H4 H H0). }
    { exact (finite_if_wrong_order (lt_transitive H3 H4)). } }
  { destruct H4.
    { split.
      { subst. assumption. }
      { subst. assumption. } }
    { split.
      { destruct (lt_total _ a c).
        { assert (a < a \/ a = a). { right. reflexivity. }
          assert (c < b \/ c = b). { left. assumption. }
          exact (subinterval_is_finite H H6 H7). }
        { destruct H5.
          { subst. specialize (finite_relation_reflexive X) as H5.
            unfold reflexive in H5. specialize (H5 c). unfold finite_relation in H5.
            destruct H5. assumption. }
          { exact (finite_if_wrong_order H5). } } }
      { assert (c < c \/ c = c). { right. reflexivity. }
        assert (a < b \/ a = b). { left. assumption. }
        exact (subinterval_is_finite H2 H5 H6). } } } }
{ destruct H3.
  { subst. split; assumption. }
  { split.
    { destruct (lt_total _ a c).
      { assert (b < a \/ b = a). { left. assumption. }
        assert (c < c \/ c = c). { right. reflexivity. }
        exact (subinterval_is_finite H0 H5 H6). }
      { destruct H4.
        { subst. specialize (finite_relation_reflexive X) as H5.
          unfold reflexive in H5. specialize (H5 c). unfold finite_relation in H5.
          destruct H5. assumption. } 
        { destruct (lt_total _ b c).
          { assert (b < a \/ b = a). { left. assumption. }
            assert (c < c \/ c = c). { right. reflexivity. }  
            exact (subinterval_is_finite H0 H6 H7). }
          { destruct H5.
            { subst. assumption. }
            { exact (finite_if_wrong_order H4). } } } } }
  { destruct (lt_total _ a c).
    { exact (finite_if_wrong_order H4). }
    { destruct H4.
      { subst. specialize (finite_relation_reflexive X) as H5.
        unfold reflexive in H5. specialize (H5 c). unfold finite_relation in H5.
        destruct H5. assumption. }
      { destruct (lt_total _ b c).
        { assert (b < c \/ b = c). { left. assumption. }
          assert (a < a \/ a = a). { right. reflexivity. }
          exact (subinterval_is_finite H1 H6 H7). }
        { destruct H5.
          { subst. assumption. }
          { exact (finite_relation_transitive_case H5 H3 H2 H1). } } } } } } }
Qed.

Definition finite_eq_relation (X : LinearOrder) : EquivRelation X :=
{|
  actual_relation := finite_relation X;
  eq_transitive := finite_relation_transitive X;
  eq_reflexive := finite_relation_reflexive X;
  eq_symmetric := finite_relation_symmetric X;
|}.

Theorem finite_relation_convex (X : LinearOrder) :
forall a b c : X, a < b -> b < c -> finite_relation X a c ->
  finite_relation X a b.
Proof.
intros. unfold finite_relation in *. destruct H1.
split.
{ assert (a < a \/ a = a). { right. reflexivity. }
  assert (b < c \/ b = c). { left. assumption. }
  exact (subinterval_is_finite H1 H3 H4). }
{ exact (finite_if_wrong_order H). }
Qed.

Definition F (X : LinearOrder) : ConvexEquivRelation X :=
{|
  eq_relation := finite_eq_relation X;
  eq_convex := finite_relation_convex X;
|}.
