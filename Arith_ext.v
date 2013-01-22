(* Some useful arithmetical theorems on nat *)
Require Export Arith.
Load Logic_ext.

(* Useful theorems missing in Arith library *)
Theorem lt_neq:
  forall n m: nat, n < m \/ m < n -> n <> m.
Proof.
  intros n m H. contradict H. rewrite H. rewrite or_dup. apply lt_irrefl.
Save.

Theorem lt_neq_iff:
  forall n m: nat, n < m \/ m < n <-> n <> m.
Proof.
  intros n m. apply iff_to_and. apply conj.
  intro H. apply lt_neq. apply H.
  intro H. apply nat_total_order. apply H.
Save.
