(** 5. Proof of the compiler, with correct states *)
Require Import Arith beta_reduction compiler krivine List lterm substitute_list substitute_varlist.

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

(** Link the lengths of the lists in tau_env *)
Lemma length_tau_env:
  forall e: krivine_env, correct_env e -> length (tau_env e) = klength e.
Proof.
  induction e; simpl; trivial.
  intro H; inversion H. clear H0 H1 H2 c0 e0 e.
  inversion H3. destruct H0. rewrite H0; simpl.
  rewrite IHe2; trivial.
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
  (* Use (closed_Access O n c) *)
  cut (n < O).
    intro Hfalse; contradict Hfalse; auto with arith.
  apply (closed_Access O n c).
  inversion H. trivial.
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
  induction st1. contradict H1. apply incorrect_Access.
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

  (* correct_state (krivine_step (KEnv (Push k1 k2) st1 st2)) *)
  simpl; apply correct_env_is_state.
  apply Correct_env; simpl; trivial.
    apply (closed_Push2 (klength st1) k1 k2); trivial.
    apply Correct_env; trivial.
    apply (closed_Push1 (klength st1) k1 k2); trivial.
Save.

(** 5.4. *)
(** Here are some lemmas with krivine_step *)
Theorem kstep_Access:
  forall (n: nat) (c: krivine_code) (e s: krivine_env),
  correct_env (KEnv (Access n c) e s) ->
  tau_env (krivine_step (KEnv (Access n c) e s)) =
    tau_env (KEnv (Access n c) e s).
Proof.
  intros n c e s H; simpl.
  inversion H. clear H0 H1 H2 c0 e0 e1.

  (* Prove n < klength e *)
  inversion H3. destruct H0. simpl in H0. inversion H0; clear H0.
  rewrite <- H6 in H1 ; clear H6 x; simpl in H1.

  (* Prove e <> Kenv_nil *)
  induction e; simpl.
    contradict H1; simpl. auto with arith.
  clear IHe1 IHe2.

  (* Prove tau_code k <> None *)
  inversion H4. clear H0 H2 H6 c0 e0 e.
  inversion H7. destruct H0.
  rewrite H0; simpl.

  (* case n = 0 is immediate *)
  induction n; simpl. rewrite H0; trivial. clear IHn.

  (* Need to prove that n < length (tau_env e2) *)
  rewrite (substitute_vl_nth_from_O n (tau_env e2) (Var n)).
  rewrite (substitute_vl_nth_from_O n (tau_env e2) (Var (S n))).
  rewrite (nth_indep (tau_env e2) (Var n) (Var (S n))); trivial.
  rewrite (length_tau_env e2); trivial.
  simpl in H1.
  auto with arith.
Save.
(*
Theorem krivine_step_is_beta_reduct:
  forall st: krivine_env, correct_state st ->
  exists t u: lterm,
    tau_state st = Some t /\
    tau_state (krivine_step st) = Some u /\
    (t = u \/ beta_reduct t u).
Proof.
  induction st; intro Hst; inversion Hst as [HstNeq HstEnv].
    contradict HstNeq; trivial.
  (* st = KEnv k st1 st2 and there are recursive hypothesis on st1 and st2 *)

  (* Induction on code *)
  induction k; unfold tau_state.

  (* k = Nop *)
  contradict HstEnv.
  apply incorrect_Nop.

  (* k = Access, st1 <> Kenv_nil *)
  inversion HstEnv. clear H H0 H1 c0 e0 e.
  induction st1. contradict HstEnv. apply incorrect_Access.
  clear IHst1_1 IHst1_2.
  induction n.
    simpl.

  simpl.
  generalize IHst1.





STOP.
  intros st H t u.
  elim H; intros H0 H1.



  inversion HstEnv. clear H H0 H1 c0 e0 e.

  (* Prove st = KEnv k st1 st2 *)
  induction st. contradict H0; trivial. simpl. clear IHst1 IHst2.
  (* Prove tau_code k = Some x *)
  inversion H1. clear H4 H5 H6 c0 e0 e.
  inversion H7. destruct H4.

  (* Introduce (krivine_step st) as st' *)
  cut (exists st': krivine_env, krivine_step st = st').
    Focus 2. exists (krivine_step st); trivial.
  intro Hst'; destruct Hst' as [st' Hst'].

  (* st' is a correct state *)
  elim (step_correctness st H).
  rewrite Hst'.
  intros H2 H3.

  (* Prove st = KEnv k st1 st2 *)
  induction st. contradict H0; trivial. clear IHst1 IHst2.
  (* Prove tau_code k = Some x *)
  inversion H1. clear H4 H5 H6 c0 e0 e.
  inversion H7. destruct H4.

  (* Same things with st', tau_code k0 = Some x0 *)
  induction st'. contradict H2; trivial. clear IHst'1 IHst'2.
  inversion H3. clear H6 H10 H11 c0 e0 e.
  inversion H12. destruct H6.

  unfold tau_state; simpl.
  rewrite H4; rewrite H6; simpl.
  induction k; simpl in H4; inversion H4.

  (* k = Access *)
  clear IHk.
  rewrite <- H15 in H5. simpl in H5. clear H4 H15 x.
  simpl.
(*
unfold krivine_step in Hst'.
  simpl.
  induction st1. contradict H1. apply incorrect_Access. clear IHst1_1 IHst1_2.
induction n. simpl.
TODO
*)

  Focus 2.
  (* k = Grab *)
  clear IHk.
  simpl in Hst'.

  induction (tau_env st'2).
    (* tau_env st'2 = nil *)
    simpl.

  induction st2; inversion Hst'.
    (* st2 = KEnv_nil -> no change *)
    simpl.
    rewrite <- H16 in H6; simpl in H6.
    rewrite H4 in H6.
    inversion H6.
    intro H20; rewrite H20.
    intro H21; inversion H21.
    apply or_introl; trivial.

    (* st2 = KEnv ... *)
    clear IHst2_1 IHst2_2.
    rewrite <- H16 in H6.
    rewrite H6 in H15; simpl in H15. inversion H15. clear H15.
    simpl.
    induction (tau_code k1).
      (* tau_code k1 = Some a *)
      simpl.

*)