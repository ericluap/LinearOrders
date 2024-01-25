From LO Require Export linearorders.

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
        simpl. simpl in hab. simpl in hbc. exact (lt_transitive hab hbc).
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
        simpl in hab. simpl in hbc. simpl. exact (lt_transitive hab hbc).
 Qed.

Theorem sum_lt_irreflexive (X Y : LinearOrder) : irreflexive (sum_lt X Y).
Proof.
intros a haa.
destruct a.
  simpl in haa. apply (lt_irreflexive s). exact haa.
  simpl in haa. apply (lt_irreflexive s). exact haa.
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