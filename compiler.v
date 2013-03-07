(** 4. Compiler *)
Require Import free_variables krivine List lterm substitute_list.

Fixpoint comp (t: lterm) : krivine_code :=
  match t with
    | Var n => Access n Nop
    | Lambda t0 => Grab (comp t0)
    | Apply t0 u => Push (comp u) (comp t0)
  end
.

(** 5. Proof of the compiler *)
(** tau is the reverse translation of the compiler *)
Fixpoint tau_code (c: krivine_code) : option lterm :=
  match c with
    | Nop => None
    | Access n c0 => Some (Var n)
    | Grab c0 => option_map Lambda (tau_code c0)
    | Push c1 c0 =>
      match tau_code c0 with
        | Some t0 => option_map (Apply t0) (tau_code c1)
        | None => None
      end
  end
.

(** Reverse translate a Krivine environment *)
Fixpoint tau_env (e: krivine_env) : list lterm :=
  match e with
    | KEnv_nil => nil
    | KEnv c0 e0 e' =>
      match tau_code c0 with
        | Some t => (subst_list t 0 (tau_env e0)) :: (tau_env e')
        | None => nil
      end
  end
.

(** Reverse translate a Krivine state,
    using a Recursive routine which works with an accumulator
 *)
Fixpoint list_lterm_to_apply (a: option lterm) (l: list lterm) : option lterm :=
  match l, a with
    | nil, _ => a
    | t :: l0, None => list_lterm_to_apply (Some t) l0
    | u :: l0, Some t => list_lterm_to_apply (Some (Apply t u)) l0
  end
.
Definition tau_state (st: krivine_env) : option lterm :=
  list_lterm_to_apply None (tau_env st)
.

(** To define correct state, define C[n] predicate ("fr_below" in code) on a code *)
Definition closed_code (n: nat) (c: krivine_code): Prop :=
   exists t: lterm, tau_code c = Some t /\ fr_below n t
.

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
Lemma not_closed_Nop:
  forall n: nat, ~ closed_code n Nop.
Proof.
  intros n H.
  inversion H.
  destruct H0.
  contradict H0.
  simpl.
  intro H0.
  inversion H0.
Save.
Lemma incorrect_Nop:
  forall (e0 e: krivine_env), ~ correct_env (KEnv Nop e0 e).
Proof.
  intros e0 e H.
  inversion H.
  contradict H3.
  apply not_closed_Nop.
Save.

(** A state with Access 0 needs a non-empty environment *)
Lemma not_closed_Access:
  forall (n: nat) (c: krivine_code), ~ closed_code O (Access n c).
Proof.
  intros n c H.
  inversion H.
  contradict H0.
  simpl.
  intro H0.
  destruct H0.
  inversion H0.
  contradict H1.
  rewrite <- H3.
  simpl.
  auto with arith.
Save.

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