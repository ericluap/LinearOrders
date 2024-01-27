From LO Require Export Product.

Structure ConvexEmbedding (X Y : LinearOrder) : Type := mkConvexEmbedding
{
convex_map :> Embedding X Y;
convexity : forall a c : X, forall y : Y, 
  ((convex_map a) < y /\ y < (convex_map c)) -> (exists b : X, convex_map b = y);
}.

(* Definition of a ConvexSuborder *)
Structure ConvexSuborder (Y : LinearOrder) : Type := mkConvexSuborder
{
source_order :> Suborder Y;
convex_embedding : forall a c : source_order, forall y : Y, 
  (embedding a) < y -> y < (embedding c) -> (exists b : source_order, embedding b = y);
}.

Arguments source_order {_}.

(* Proving that the set {x : A, P} is a convex suborder of A if P is a convex predicate *)
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

(* Showing that xY is a convex suborder of XY for any x : X *)
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

Structure ConvexEquivRelation (X : LinearOrder) := mkEquivRelation {
  eq_relation :> EquivRelation X;
  eq_convex : forall a b c : X, a < b -> b < c -> 
    actual_relation X eq_relation a c -> actual_relation X eq_relation a b;
}.