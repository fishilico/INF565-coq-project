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

Theorem closed_code_id:
  closed_code O krivine_id.
Proof.
  unfold closed_code.
  exists l_id.
  elim tau_id.
  apply conj; trivial.
  apply closed_id.
Save.

Theorem correct_id:
  correct_state kstate_id.
Proof.
  apply correct_env_is_state.
  apply Correct_env; simpl.
  apply closed_code_id.
  apply Correct_env_nil.
  apply Correct_env_nil.
Save.

(** Identity is a final state in krivine machine *)
Theorem final_step_id:
  krivine_step kstate_id = kstate_id.
Proof.
  trivial.
Save.


(** Second example, with apply *)
Definition l_id2 : lterm := Apply l_id l_id
.
Definition krivine_id2 : krivine_code := Push krivine_id krivine_id
.
Definition kstate_id2 : krivine_env := krivine_state krivine_id2 KEnv_nil KEnv_nil
.
Theorem closed_id2:
  closed l_id2.
Proof.
  unfold closed; unfold l_id2. simpl.
  auto with arith.
Save.
Theorem compile_id2:
  comp l_id2 = krivine_id2.
Proof.
  unfold l_id2. unfold krivine_id2. trivial.
Save.
Theorem tau_id2:
  tau_code krivine_id2 = Some l_id2.
Proof.
  unfold l_id2. unfold krivine_id2. trivial.
Save.
Theorem closed_code_id2:
  closed_code O krivine_id2.
Proof.
  unfold closed_code.
  exists l_id2.
  elim tau_id2.
  apply conj; trivial.
  apply closed_id2.
Save.
Theorem correct_id2:
  correct_state kstate_id2.
Proof.
  apply correct_env_is_state.
  apply Correct_env; simpl.
  apply closed_code_id2.
  apply Correct_env_nil.
  apply Correct_env_nil.
Save.

(** Krivine steps on id2 *)
Theorem krivine_steps_id2:
  krivine_step kstate_id2 = krivine_state krivine_id KEnv_nil kstate_id /\
  krivine_step (krivine_step kstate_id2) =
    krivine_state (Access 0 Nop) kstate_id KEnv_nil /\
  krivine_step (krivine_step (krivine_step kstate_id2)) = kstate_id.
Proof.
  apply conj; trivial.
  apply conj; trivial.
Save.
