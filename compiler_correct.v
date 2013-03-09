(** 5. Proof of the compiler, with correct states *)
Require Import Arith beta_reduction compiler free_variables krivine.
Require Import List lterm substitute_list substitute_varlist.

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
(** tau_state is never None for correct state *)
Lemma tau_state_correct_is_some:
  forall st: krivine_env, correct_state st -> exists t: lterm, tau_state st = Some t.
Proof.
  (* st is not nil *)
  induction st; intro H; inversion H. contradict H0; trivial.
  unfold tau_state; simpl.
  inversion H1. clear H2 H3 H4 c0 e0 e.
  inversion H5. destruct H2. rewrite H2; simpl.
  apply list_lterm_to_apply_is_some.
Save.

(** Lemma for Beta-reduction and tau_state, which uses list_lterm_to_apply *)
Lemma beta_reduct_list_lterm_to_apply:
  forall (l: list lterm) (t u t' u': lterm), beta_reduct t u ->
    Some t' = list_lterm_to_apply (Some t) l ->
    Some u' = list_lterm_to_apply (Some u) l ->
    beta_reduct t' u'.
Proof.
  induction l; intros t u t' u' H; simpl; intros Ht Hu.
    inversion Ht; inversion Hu; trivial.
  apply (IHl (Apply t a) (Apply u a)); trivial.
  apply Beta_reduct_close_apply1; trivial.
Save.

(** A correct environment is closed *)
Lemma closed_correct_env:
  forall e: krivine_env, correct_env e -> fr_below_list O (tau_env e).
Proof.
  induction e; simpl; trivial; intro H.
  inversion H. clear H0 H1 H2 c0 e0 e.
  inversion H3. destruct H0. rewrite H0; simpl.
  apply conj.
    apply substitute_list_closed.
      apply IHe1; trivial.
      rewrite length_tau_env; trivial.
    apply IHe2; trivial.
Save.

(** Here are some lemmas with krivine_step *)
Lemma tau_env_kstep_Access:
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

Lemma tau_state_kstep_Access:
  forall (n: nat) (c: krivine_code) (e s: krivine_env),
  correct_env (KEnv (Access n c) e s) ->
  tau_state (krivine_step (KEnv (Access n c) e s)) =
    tau_state (KEnv (Access n c) e s).
Proof.
  intros n c e s H; unfold tau_state.
  rewrite tau_env_kstep_Access; trivial.
Save.

Lemma tau_state_kstep_Push:
  forall (c0 c: krivine_code) (e s: krivine_env),
  correct_env (KEnv (Push c0 c) e s) ->
  tau_state (krivine_step (KEnv (Push c0 c) e s)) =
    tau_state (KEnv (Push c0 c) e s).
Proof.
  intros c0 c e s H; unfold tau_state; simpl.
  inversion H. clear H0 H1 H2 c1 e0 e1.

  (* Prove tau_code c <> None *)
  inversion H3. destruct H0. simpl in H0.
  cut (exists ot: option lterm, tau_code c = ot).
    Focus 2. exists (tau_code c); trivial.
  intro Hot; destruct Hot as [ot Hot].
  rewrite Hot in H0.
  induction ot. Focus 2. inversion H0.
  rewrite Hot.

  (* Prove tau_code c0 <> None *)
  cut (exists ot0: option lterm, tau_code c0 = ot0).
    Focus 2. exists (tau_code c0); trivial.
  intro Hot0; destruct Hot0 as [ot0 Hot0].
  rewrite Hot0 in H0.
  induction ot0. Focus 2. inversion H0.
  rewrite Hot0; trivial.
Save.

Lemma tau_state_kstep_Grab:
  forall (c: krivine_code) (e: krivine_env) (s: krivine_env) (t u: lterm),
  correct_env (KEnv (Grab c) e s) ->
  tau_state (KEnv (Grab c) e s) = Some t ->
  tau_state (krivine_step (KEnv (Grab c) e s)) = Some u ->
  (t = u \/ beta_reduct t u).
Proof.
  intros c e s t u H. unfold tau_state; simpl.
  inversion H. clear H0 H1 H2 c0 e0 e1.

  (* Prove tau_code c <> None *)
  inversion H3. destruct H0. simpl in H0.
  cut (exists ot: option lterm, tau_code c = ot).
    Focus 2. exists (tau_code c); trivial.
  intro Hc; destruct Hc as [ot Hc].
  rewrite Hc; rewrite Hc in H0.
  induction ot; simpl. Focus 2. inversion H0.

  (* Remove variable x *)
  simpl in H0; inversion H0 as [Hx]; clear H0.
  rewrite <- Hx in H1; simpl in H1; clear Hx x.

  (* If the stack is empty, krivine_step is identity, this is almost trivial *)
  induction s; simpl; rewrite Hc; simpl.
    intros Ht Hu. inversion Ht as [Ht']. rewrite Ht'; rewrite Ht' in Hu.
    inversion Hu. auto.
  clear IHs1 IHs2.
  (* Now s = KEnv k s1 s2 *)

  (* Prove tau_code k <> None *)
  inversion H5. clear H0 H2 H6 c0 e0 e1.
  inversion H7. destruct H0.
  rewrite H0; simpl.

  (* Use beta_reduct_list_lterm_to_apply *)
  intros Ht Hu. apply or_intror.
  apply (beta_reduct_list_lterm_to_apply (tau_env s2)
      (Apply (Lambda (subst_list a 1 (tau_env e))) (subst_list x 0 (tau_env s1)))
      (subst_list a 0 (subst_list x 0 (tau_env s1) :: tau_env e))).
  Focus 2. rewrite Ht; trivial.
  Focus 2. rewrite Hu; trivial.

  (* Prove beta_reduct *)
  rewrite (substitute_list_cons_free_eq a (tau_env e) O (subst_list x 0 (tau_env s1))).
  rewrite substitute_list_singleton.
  apply Beta_reduct_step.

  (* Prove closed_list (tau_env e) *)
  apply closed_correct_env; trivial.
Save.

Lemma tau_state_kstep_all:
  forall (st: krivine_env) (t u: lterm), correct_state st ->
  tau_state st = Some t ->
  tau_state (krivine_step st) = Some u ->
    (t = u \/ beta_reduct t u).
Proof.
  intros st t u Hst Ht Hu.

  (* st = KEnv k st1 st2 *)
  inversion Hst as [HstNeq HstEnv].
  induction st. contradict HstNeq; trivial.
  clear IHst1 IHst2.

  (* Induction on code *)
  induction k.

  (* Nop is incorrect *)
  contradict HstEnv.
  apply incorrect_Nop.

  (* Access *)
  rewrite (tau_state_kstep_Access n k st1 st2) in Hu; trivial.
  rewrite Hu in Ht. inversion Ht. auto.

  (* Grab *)
  apply (tau_state_kstep_Grab k st1 st2); trivial.

  (* Push *)
  rewrite (tau_state_kstep_Push k1 k2 st1 st2) in Hu; trivial.
  rewrite Hu in Ht. inversion Ht. auto.
Save.

(** 5.4. Theorem *)
Theorem krivine_step_is_beta_reduct:
  forall st: krivine_env, correct_state st ->
  exists t: lterm, Some t = tau_state st ->
  exists u: lterm, Some u = tau_state (krivine_step st) ->
    (t = u \/ beta_reduct t u).
Proof.
  intros st Hst.

  (* Use tau_state_correct_is_some *)
  elim (tau_state_correct_is_some st); trivial.
  intros t Ht. exists t; intro Hcleared; clear Hcleared.
  elim (tau_state_correct_is_some (krivine_step st)).
    Focus 2. apply step_correctness; trivial.
  intros u Hu. exists u; intro Hcleared; clear Hcleared.

  apply (tau_state_kstep_all st); trivial.
Save.

(** 5.5. *)
(** Extend 5.3 to krivine_step_star *)
Theorem krivine_step_star_correctness:
  forall st st': krivine_env, krivine_step_star st st' ->
  correct_state st -> correct_state st'.
Proof.
  intros st st' H.
  induction H; trivial.
  intro H0.
  apply IHkrivine_step_star.
  apply step_correctness; trivial.
Save.

(** Extend 5.4 to krivine_step_star *)
Lemma tau_state_kstep_star_all:
  forall (st st': krivine_env),
  krivine_step_star st st' -> correct_state st ->
    forall (t u: lterm),
    tau_state st = Some t -> tau_state st' = Some u ->
    beta_reduct_star t u.
Proof.
  intros st st' H.
  induction H; intros Hst t v Ht Hv.
    rewrite Hv in Ht. inversion Ht. apply Beta_reduct_star_eq.
  (* Introduce Some u = tau_state (krivine_step st) *)
  elim (tau_state_correct_is_some (krivine_step st)).
    Focus 2. apply step_correctness; trivial.
  intros u Hu.

  (* t and u may be equals *)
  elim (tau_state_kstep_all st t u); trivial; intro H0.
    (* t = u *)
    rewrite H0.
    apply IHkrivine_step_star; trivial.
    apply step_correctness; trivial.

    (* beta_reduct t u *)
    apply (Beta_reduct_star_step t u v); trivial.
    apply IHkrivine_step_star; trivial.
    apply step_correctness; trivial.
Save.

Theorem krivine_step_is_beta_reduct_star:
  forall st st': krivine_env, krivine_step_star st st' -> correct_state st ->
  exists t: lterm, Some t = tau_state st ->
  exists u: lterm, Some u = tau_state st' ->
    beta_reduct_star t u.
Proof.
  intros st st' H Hst.
  elim (tau_state_correct_is_some st); trivial.
  intros t Ht. exists t; intro Hcleared; clear Hcleared.
  elim (tau_state_correct_is_some st').
    Focus 2. apply (krivine_step_star_correctness st st'); trivial.
  intros u Hu. exists u; intro Hcleared; clear Hcleared.
  apply (tau_state_kstep_star_all st st'); trivial.
Save.
