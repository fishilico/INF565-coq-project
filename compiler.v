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

(** Here are some theorems using closed_code *)
Theorem not_closed_Nop:
  forall n: nat, ~ closed_code n Nop.
Proof.
  intros n H.
  inversion H.
  elim H0; simpl.
  intro H1; inversion H1.
Save.

Theorem closed_Access:
  forall (n m: nat) (c: krivine_code),
  closed_code n (Access m c) -> m < n.
Proof.
  intros n m c H.
  inversion H.
  elim H0; simpl.
  intro H1; inversion H1.
  trivial.
Save.

Theorem closed_Access_iff:
  forall (n m: nat) (c: krivine_code),
  m < n -> closed_code n (Access m c).
Proof.
  intros n m c H.
  unfold closed_code; simpl.
  exists (Var m).
  apply conj; trivial.
Save.

Theorem closed_Grab_S:
  forall (n: nat) (c: krivine_code),
  closed_code n (Grab c) -> closed_code (S n) c.
Proof.
  intros n c.

  (* We need to introduce (tau_code c) as a (option lterm) *)
  cut (exists ot: option lterm, tau_code c = ot).
    Focus 2. exists (tau_code c); trivial.
  intro Hot; destruct Hot as [ot Hot].

  (* Clear any reference to (tau_code c) *)
  unfold closed_code; simpl; rewrite Hot.
  clear Hot c.

  intro H; destruct H as [t H]. destruct H.

  (* Prove that ot is (Some a) *)
  induction ot; inversion H.
  exists a; apply conj; trivial.
  generalize H0.
  rewrite <- H2; trivial.
Save.

(** Intermediate lemma for Push *)
Lemma closed_Push_internal:
  forall (n: nat) (c0 c: krivine_code), closed_code n (Push c0 c) ->
  exists (t t0: lterm),
  tau_code c = Some t /\ tau_code c0 = Some t0 /\ fr_below n (Apply t t0).
Proof.
  intros n c0 c.
  unfold closed_code; simpl.

  (* Introduce (tau_code c) : (option lterm) *)
  cut (exists ot: option lterm, tau_code c = ot).
    Focus 2. exists (tau_code c); trivial.
  intro Hot; destruct Hot as [ot Hot].
  rewrite Hot. clear Hot c.

  (* Introduce (tau_code c0) : (option lterm) *)
  cut (exists ot: option lterm, tau_code c0 = ot).
    Focus 2. exists (tau_code c0); trivial.
  intro Hot; destruct Hot as [ot0 Hot].
  rewrite Hot. clear Hot c0.

  intro H; destruct H as [t H]. destruct H.
  induction ot; inversion H. clear H2.
  induction ot0; inversion H.
  exists a; exists a0; apply conj; trivial; apply conj; trivial.
  generalize H0. rewrite <- H2; trivial.
Save.

Theorem closed_Push1:
  forall (n: nat) (c0 c: krivine_code),
  closed_code n (Push c0 c) -> closed_code n c0.
Proof.
  intros n c0 c H.
  unfold closed_code; simpl.
  elim (closed_Push_internal n c0 c H).
  intros x H0.
  destruct H0 as [t0 H0]. destruct H0; destruct H1.
  generalize H2; clear H2; simpl; intro H2.
  destruct H2.
  exists t0; apply conj; trivial.
Save.

Theorem closed_Push2:
  forall (n: nat) (c0 c: krivine_code),
  closed_code n (Push c0 c) -> closed_code n c.
Proof.
  intros n c0 c H.
  unfold closed_code; simpl.
  elim (closed_Push_internal n c0 c H).
  intros x H0.
  destruct H0 as [t0 H0]. destruct H0; destruct H1.
  generalize H2; clear H2; simpl; intro H2.
  destruct H2.
  exists x; apply conj; trivial.
Save.
