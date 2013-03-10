Require Import Arith List lterm.

(** 1.2. Predicate: every free variable has an index below n *)
Fixpoint closed_n (n: nat) (t: lterm) : Prop :=
  match t with
    | Var x => x < n
    | Lambda u => closed_n (S n) u
    | Apply u v => (closed_n n u) /\ (closed_n n v)
  end
.

(** Closed term *)
Definition closed (t: lterm) : Prop :=
  closed_n 0 t
.

(** closed_n is still True when n increases *)
Lemma closed_n_S:
  forall (t: lterm) (n: nat),
  closed_n n t -> closed_n (S n) t.
Proof.
  induction t; simpl; intros i H.
    auto with arith.
    apply IHt; trivial.
    destruct H. split.
      apply IHt1; trivial.
      apply IHt2; trivial.
Save.

Theorem closed_n_incr:
  forall (t: lterm) (n m: nat),
  closed_n n t -> n <= m -> closed_n m t.
Proof.
  intros t n; induction m; simpl; intros H H0.
    (* m = 0 *)
    generalize H.
    elim (le_n_0_eq n); trivial.
    (* m = S m *)
    elim (le_lt_eq_dec n (S m)); trivial; clear H0; intro H0.
      (* n < S m *)
      apply (closed_n_S t m).
      apply IHm; trivial.
      auto with arith.
      (* n = S m *)
      rewrite <- H0; trivial.
Save.

(** forall u in ul, closed_n n u *)
Fixpoint closed_n_list (n: nat) (ul: list lterm) : Prop :=
  match ul with
    | nil => True
    | u :: l => (closed_n n u) /\ (closed_n_list n l)
  end
.

Theorem closed_n_list_forall:
  forall (n: nat) (ul: list lterm),
  closed_n_list n ul -> (forall u: lterm, In u ul -> closed_n n u).
Proof.
  intro n; induction ul; simpl; intros H u H0.
    contradict H0.
    destruct H. destruct H0.
      rewrite <- H0; trivial.
      apply IHul; trivial.
Save.

(** closed_n_list is still True when n increases *)
Theorem closed_n_list_S:
  forall (n: nat) (ul: list lterm),
  closed_n_list n ul -> closed_n_list (S n) ul.
Proof.
  induction ul; simpl; trivial.
  intro H; destruct H.
  split.
    apply closed_n_S; trivial.
    apply IHul; trivial.
Save.
