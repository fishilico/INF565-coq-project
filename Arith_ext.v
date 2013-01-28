(* Some useful arithmetical theorems on nat missing in Arith library *)
Require Export Arith.

Theorem lt_neq:
  forall n m: nat, n < m -> n <> m.
Proof.
  intros n m H. contradict H. rewrite H. apply lt_irrefl.
Save.

Theorem lt_neq_sym:
  forall n m: nat, n < m -> m <> n.
Proof.
  intros n m H. contradict H. rewrite H. apply lt_irrefl.
Save.

Theorem minus_plus_simpl:
  forall n m p: nat, n - (m + p) = n - m - p.
Proof.
  induction n; induction m; induction p; simpl; trivial.
Save.