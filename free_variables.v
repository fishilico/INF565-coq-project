Require Import Arith_ext List lterm.

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
  induction t; simpl.
    auto with arith.
    intros n H. apply (IHt (S n)); trivial.
    intros n H. apply conj.
      apply IHt1; apply H.
      apply IHt2; apply H.
Save.

Theorem fr_below_incr:
  forall (t: lterm) (n m: nat),
  fr_below n t /\ n <= m -> fr_below m t.
Proof.
  intros t n; induction m; intro H; destruct H.
    cut (O = n).
      intro H1; rewrite H1; trivial.
      auto with arith.

    cut (n < S m \/ n = S m).
      intro H1; destruct H1.
        apply (fr_below_S t m). apply IHm.
        apply conj; trivial; auto with arith.

        rewrite <- H1; trivial.
      apply (le_lt_or_eq n (S m)); trivial.
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
