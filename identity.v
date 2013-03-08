(** Example of function: the identity *)
Require Import compiler free_variables krivine lterm.

Definition l_id: lterm := Lambda (Var O)
.

Definition krivine_id : krivine_code := Grab (Access 0 Nop)
.


(** Identity is closed *)
Lemma closed_id:
  closed l_id.
Proof.
  unfold closed.
  unfold l_id.
  simpl.
  auto with arith.
Save.

(** Compilation *)
Lemma compile_id:
  comp l_id = krivine_id.
Proof.
  unfold l_id.
  unfold krivine_id.
  trivial.
Save.

(** Reverse compilation *)
Lemma tau_id:
  tau_code krivine_id = Some l_id.
Proof.
  unfold l_id.
  unfold krivine_id.
  trivial.
Save.
