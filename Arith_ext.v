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

Theorem plus_Sn:
  forall n: nat, S n = n + 1.
Proof.
  intro n. rewrite (plus_comm n 1). trivial.
Save.

Theorem lt_S_lt_or_eq:
  forall (n m: nat), n < S m -> n < m \/ n = m.
Proof.
  intros n m H.
  apply (le_lt_or_eq n m).
  apply (lt_n_Sm_le n m).
  apply H.
Save.

Theorem le_exists_diff:
  forall (n m: nat), n <= m -> exists d: nat, m = n + d.
Proof.
  intros n m H.
  exists (m - n).
  apply (le_plus_minus n m).
  apply H.
Save.

(* Let's proove trivial things *)
Theorem neq_or_eq:
  forall (n m: nat), n = m \/ n <> m.
Proof.
  intros n m.
  cut (n <= m \/ m < n).
    intro H; destruct H.
      cut (n < m \/ n = m).
        intro H0; destruct H0.
          apply or_intror. apply lt_neq; trivial.
          apply or_introl; trivial.
        apply (le_lt_or_eq n m); trivial.
      apply or_intror. apply lt_neq_sym; trivial.
    apply le_or_lt.
Save.
