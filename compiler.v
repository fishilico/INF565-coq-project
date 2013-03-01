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

Lemma correct_state_nonnil:
  forall (c0: krivine_code) (e0 e: krivine_env),
  correct_env (KEnv c0 e0 e) -> correct_state (KEnv c0 e0 e).
Proof.
  intros c0 e0 e H.
  unfold correct_state.
  apply conj; trivial.
  intro H0. inversion H0.
Save.

(** Proofs *)
(** 5.2. *)
Theorem compile_term_tau_ident:
  forall t: lterm, tau_code (comp t) = Some t.
Proof.
  induction t; simpl; trivial.
  rewrite IHt; trivial.
  rewrite IHt1; rewrite IHt2; trivial.
Save.
