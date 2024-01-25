From LO Require Export PredOrder.
From LO Require Export Omega.
Require Import Classical.
Require Import FunctionalExtensionality.

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

(* Defining the produt of two linear orders specifically *)
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