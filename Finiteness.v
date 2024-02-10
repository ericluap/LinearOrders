From LO Require Export Omega.
From LO Require Export PredOrder.

Definition is_finite (X : LinearOrder) :=
   exists n : omega, exists p : Embedding X {m : omega, m < n}, True.

Definition is_infinite (X : LinearOrder) := ~ is_finite X.