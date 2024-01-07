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
f : X -> Y;
order_preserving : forall a b : X, a < b -> f a < f b
}.


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




