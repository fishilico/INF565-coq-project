(** Example of function: the identity *)
Require Import beta_reduction compiler compiler_correct free_variables krivine lterm.

Definition l_id: lterm := Lambda (Var O)
.

Definition krivine_id : krivine_code := Grab (Access 0 Nop)
.

(** Identity is closed *)
Theorem closed_id:
  closed l_id.
Proof.
  unfold closed.
  unfold l_id.
  simpl.
  auto with arith.
Save.

(** Compilation *)
Theorem compile_id:
  comp l_id = krivine_id.
Proof.
  unfold l_id.
  unfold krivine_id.
  trivial.
Save.

(** Reverse compilation *)
Theorem tau_id:
  tau_code krivine_id = Some l_id.
Proof.
  unfold l_id.
  unfold krivine_id.
  trivial.
Save.

(** Correct state *)
Definition kstate_id : krivine_env := krivine_state krivine_id KEnv_nil KEnv_nil
.

Theorem correct_id:
  correct_state kstate_id.
Proof.
  apply correct_env_is_state.
  apply Correct_env; simpl.
    unfold closed_code.
    exists l_id.
    elim tau_id.
    apply conj; trivial.
    apply closed_id.
  apply Correct_env_nil.
  apply Correct_env_nil.
Save.

(** Identity is a final state in krivine machine *)
Theorem final_step:
  krivine_step kstate_id = kstate_id.
Proof.
  unfold kstate_id.
  trivial.
Save.
