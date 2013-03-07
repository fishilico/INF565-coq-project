(** 5. Proof of the compiler, with correct states *)
Require Import compiler krivine List lterm.

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

(** Proofs *)
(** 5.2. *)
Theorem compile_term_tau_ident:
  forall t: lterm, tau_code (comp t) = Some t.
Proof.
  induction t; simpl; trivial.
  rewrite IHt; trivial.
  rewrite IHt1; rewrite IHt2; trivial.
Save.

(** 5.3. *)
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

(** A state with Access 0 needs a non-empty environment *)


Lemma incorrect_Access:
  forall (n: nat) (c: krivine_code) (s: krivine_env),
  ~ correct_env (KEnv (Access n c) KEnv_nil s).
Proof.
  intros n c s H.
  inversion H.
  contradict H3; simpl.
  apply not_closed_Access.
Save.
(*
Theorem step_correctness:
  forall st: krivine_env, correct_state st -> correct_state (krivine_step st).
Proof.
  induction st; trivial.
  induction k; trivial; intro H.

  (* State: Nop st1 st2 *)
  inversion H.
  contradict H1.
  apply incorrect_Nop.

  (* State: (Access n k) st1 st2 *)
  inversion H.
(* Not ended *)

*)
