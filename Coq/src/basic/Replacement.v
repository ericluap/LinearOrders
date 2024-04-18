From LO Require Export Product.

T

Inductive replacement_set {X : LinearOrder} (map : X -> LinearOrder) :=
| intro_rep (x : X) (z : map x).

Definition replacement_order 
{X : LinearOrder} (map : X -> LinearOrder) : 
relation (replacement_set map) :=
fun a b : replacement_set map =>
match a, b with
| intro_rep _ a_zero a_one, intro_rep _ b_zero b_one =>
  (a_zero < b_zero) \/ (a_zero = b_zero /\ a_one < b_one)
end.


fun a b : product_set map =>
exists i : index, ((a i) < (b i)) /\ (forall j : index, j < i -> a j = b j).
