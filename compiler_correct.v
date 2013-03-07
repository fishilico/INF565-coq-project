(** 5. Proof of the compiler, with correct states *)
Require Import Arith compiler krivine List lterm.

(** Correct environment/stack/state (that's the same object) *)
Inductive correct_env: krivine_env -> Prop :=
  | Correct_env_nil: correct_env KEnv_nil
  | Correct_env:
    forall (c0: krivine_code) (e0 e: krivine_env),
    closed_code (klength e0) c0 -> correct_env e0 -> correct_env e ->
    correct_env (KEnv c0 e0 e)
.

(** A correct state is a correct non-empty environment *)
Definition correct_state (st: krivine_env) : Prop :=
  st <> KEnv_nil /\ correct_env st
.

(** A non-empty correct environment is a correct state *)
Lemma correct_env_is_state:
  forall (c0: krivine_code) (e0 e: krivine_env),
  correct_env (KEnv c0 e0 e) -> correct_state (KEnv c0 e0 e).
Proof.
  intros c0 e0 e H.
  unfold correct_state.
  apply conj; trivial.
  intro H0. inversion H0.
Save.

(** An environment with Nop as code is always incorrect *)
Lemma incorrect_Nop:
  forall (e0 e: krivine_env), ~ correct_env (KEnv Nop e0 e).
Proof.
  intros e0 e H.
  inversion H.
  contradict H3.
  apply not_closed_Nop.
Save.

(** A state with Access is invalid with an empty environment *)
Lemma incorrect_Access:
  forall (n: nat) (c: krivine_code) (s: krivine_env),
  ~ correct_env (KEnv (Access n c) KEnv_nil s).
Proof.
  intros n c s H.
  inversion H. clear H0 H1 H2 c0 e0 e.
  generalize H3; simpl; intro H0. clear H3.
  cut (n < O).
    intro H1; contradict H1; auto with arith.
  apply (closed_Access O n c); trivial.
Save.

(** 5.3. *)
Theorem step_correctness:
  forall st: krivine_env, correct_state st -> correct_state (krivine_step st).
Proof.
  (* Use correct_env instead of correct_state in hypothesis *)
  induction st; trivial. clear IHst1 IHst2.
  intro H. inversion H. clear H H0.
  induction k; inversion H1; clear H H0 H2 c0 e0 e.

  (* correct_state (krivine_step (KEnv Nop st1 st2)) *)
  contradict H1.
  apply incorrect_Nop.

  (* correct_state (krivine_step (KEnv (Access n k) st1 st2)) *)
  induction st1.
    contradict H1. apply incorrect_Access.
  clear IHst1_1 IHst1_2.
  (* Now st1 = KEnv k0 st1_1 st1_2 *)
  inversion H4. clear H H0 H2 c0 e0 e.
  simpl.
  induction n; apply correct_env_is_state; apply Correct_env; trivial.
  apply closed_Access_iff.
  apply lt_S_n.
  generalize H3; simpl.
  apply closed_Access.

  (* correct_state (krivine_step (KEnv (Grab k) st1 st2)) *)
  induction st2; simpl; apply correct_env_is_state; trivial.
  clear IHst2_1 IHst2_2.
  inversion H5. clear H H0 H2 c0 e0 e.
  apply Correct_env; simpl; trivial.
    apply closed_Grab_S; trivial.
    apply Correct_env; trivial.
