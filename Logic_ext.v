(* Some useful logic theorems *)
Require Export Logic.

(* Duplicate a Prop with or *)
Theorem or_dup:
  forall A: Prop, A \/ A <-> A.
Proof.
  intro A.
  apply iff_to_and. apply conj.
    intro H. destruct H. trivial. trivial.
    apply or_introl.
Save.

(* Duplicate a Prop with and *)
Theorem and_repeat:
  forall A: Prop, A /\ A <-> A.
Proof.
  intro A.
  apply iff_to_and. apply conj.
    intro H. destruct H. trivial.
    intro H. apply conj. trivial. trivial.
Save.
