From LO Require Export Suborder.

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