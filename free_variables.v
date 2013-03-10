Require Import Arith List lterm.

(* Predicate: every free variable has an index below n *)
Fixpoint fr_below (n: nat) (t: lterm) : Prop :=
  match t with
    | Var x => x < n
    | Lambda u => fr_below (S n) u
    | Apply u v => (fr_below n u) /\ (fr_below n v)
  end
.

(* Closed term *)
Definition closed (t: lterm) : Prop :=
  fr_below 0 t
.

(* fr_below is still True when n increases *)
Theorem fr_below_S:
  forall (t: lterm) (n: nat),
  fr_below n t -> fr_below (S n) t.
Proof.
  induction t; simpl; intros i H.
    auto with arith.
    apply IHt; trivial.
    destruct H. split.
      apply IHt1; trivial.
      apply IHt2; trivial.
Save.

Theorem fr_below_incr:
  forall (t: lterm) (n m: nat),
  fr_below n t -> n <= m -> fr_below m t.
Proof.
  intros t n; induction m; simpl; intros H H0.
    (* m = 0 *)
    generalize H.
    elim (le_n_0_eq n); trivial.
    (* m = S m *)
    elim (le_lt_eq_dec n (S m)); trivial; clear H0; intro H0.
      (* n < S m *)
      apply (fr_below_S t m).
      apply IHm; trivial.
      auto with arith.
      (* n = S m *)
      rewrite <- H0; trivial.
Save.

(* forall u in ul, fr_below n u *)
Fixpoint fr_below_list (n: nat) (ul: list lterm) : Prop :=
  match ul with
    | nil => True
    | u :: l => (fr_below n u) /\ (fr_below_list n l)
  end
.

Lemma fr_below_list_forall:
  forall (n: nat) (ul: list lterm),
  fr_below_list n ul -> (forall u: lterm, In u ul -> fr_below n u).
Proof.
  intro n; induction ul; simpl; intros H u H0.
    contradict H0.
    destruct H. destruct H0.
      rewrite <- H0; trivial.
      apply IHul; trivial.
Save.

(* fr_below_list is still True when n increases *)
Theorem fr_below_list_S:
  forall (n: nat) (ul: list lterm),
  fr_below_list n ul -> fr_below_list (S n) ul.
Proof.
  induction ul; simpl; trivial.
  intro H; destruct H.
  split.
    apply fr_below_S; trivial.
    apply IHul; trivial.
Save.
