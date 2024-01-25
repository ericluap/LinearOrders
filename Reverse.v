From LO Require Export linearorders.

(* Proving that the reverse of the relation of a linear order is still a linear order *)
Theorem reverse_transitive (X : LinearOrder) : transitive (reverse_relation X.(lt)).
Proof.
unfold reverse_relation. unfold transitive.
intros a b c hba hcb.
exact (lt_transitive hcb hba).
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