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

(** 5.2. *)
Theorem compile_term_tau_ident:
  forall t: lterm, tau_code (comp t) = Some t.
Proof.
  induction t; simpl; trivial.
  rewrite IHt; trivial.
  rewrite IHt1; rewrite IHt2; trivial.
Save.

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

(** Here are some lemmas using closed_code *)
Lemma not_closed_Nop:
  forall n: nat, ~ closed_code n Nop.
Proof.
  intros n H.
  inversion H.
  elim H0; simpl.
  intro H1; inversion H1.
Save.

Lemma closed_Access:
  forall (n m: nat) (c: krivine_code),
  closed_code n (Access m c) -> m < n.
Proof.
  intros n m c H.
  inversion H.
  elim H0; simpl.
  intro H1; inversion H1.
  trivial.
Save.

Lemma closed_Access_iff:
  forall (n m: nat) (c: krivine_code),
  m < n -> closed_code n (Access m c).
Proof.
  intros n m c H.
  unfold closed_code; simpl.
  exists (Var m).
  apply conj; trivial.
Save.

Lemma closed_Grab_S:
  forall (n: nat) (c: krivine_code),
  closed_code n (Grab c) -> closed_code (S n) c.
Proof.
  intros n c.
  unfold closed_code; simpl.

  (* We need to introduce (tau_code c) as a (option lterm) *)
  cut (exists ot: option lterm, tau_code c = ot).
    Focus 2. exists (tau_code c); trivial.
  intro Hot; destruct Hot as [ot Hot].

  (* Prove that ot is (Some a) *)
  induction ot.
    Focus 2. rewrite Hot; simpl.
    intro H; destruct H as [t H]. destruct H.
    inversion H.

  rewrite Hot; simpl.
  intro H; destruct H as [t H]. destruct H.
  inversion H.
  exists a; apply conj; trivial.
  generalize H0.
  rewrite <- H2; simpl; trivial.
Save.
