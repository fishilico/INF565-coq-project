Require Import Arith_ext List lterm substitution.

(* Substitution of variable x in a list i->u0, i+1->u1, i+2->u2, ...
 * Return d by default
 *)
Fixpoint subst_var_list (x i: nat) (ul: list lterm) (d: lterm) : lterm :=
  match ul, i, x with
    | nil, _, _ => d
    | t :: _, O, O => t
    | _ :: vl, O, S y => subst_var_list y O vl d
    | _ :: _, S _, O => d
    | _ :: _, S j, S y => subst_var_list y j ul d
  end
.

Lemma substitute_vl_nil:
  forall (n x: nat) (d: lterm), subst_var_list n x nil d = d.
Proof.
  induction n; trivial.
Save.
Hint Resolve substitute_vl_nil : substitute.

Lemma substitute_vl_eq:
  forall (n: nat) (u: lterm) (ul: list lterm) (d: lterm),
  subst_var_list n n (u :: ul) d = u.
Proof.
  induction n; simpl; trivial.
Save.
Hint Resolve substitute_vl_eq : substitute.

(* (Var n)[(n + a + 1) <- ul_0, ul_1, ...] = (Var n), a is called "diff" *)
Lemma substitute_vl_lt_with_diff:
  forall (n a: nat) (ul: list lterm) (d: lterm),
  subst_var_list n (n + 1 + a) ul d = d.
Proof.
  induction n; induction a; induction ul; intro d; simpl; trivial.
Save.

Lemma substitute_vl_lt:
  forall (x i: nat) (ul: list lterm) (d: lterm),
  x < i -> subst_var_list x i ul d = d.
Proof.
  intros x i ul d H.
  cut (i = x + 1 + (i - (x + 1))).
    intro H0; rewrite H0. auto.
    apply (substitute_vl_lt_with_diff x (i - (x + 1)) ul d).

    apply (le_plus_minus (x + 1) i).
    rewrite <- (plus_Sn x).
    apply (lt_le_S x i).
    apply H.
Save.
Hint Immediate substitute_vl_lt : substitute.

(* The proof of this lemme uses an induction on i which impacts the order of parameters *)
Lemma substitute_vl_gt_prooforder:
  forall (i x: nat) (u: lterm) (ul: list lterm) (d: lterm),
  x > i -> subst_var_list x i (u :: ul) d = subst_var_list x (S i) ul d.
Proof.
  induction i; intros x u ul d H; simpl; cut (x = S (pred x)).
    intro H0; rewrite H0.
    induction ul; simpl; auto with substitute.

    apply (S_pred x 0); trivial.

    intro H0; rewrite H0; simpl.
    rewrite (IHi (pred x) u ul d).
      induction ul; auto with substitute.
      auto with arith.
    apply (S_pred x (S i)); trivial.
Save.

(* Same as above, change parameters order *)
Lemma substitute_vl_gt:
  forall (x i: nat) (u: lterm) (ul: list lterm) (d: lterm),
  x > i -> subst_var_list x i (u :: ul) d = subst_var_list x (S i) ul d.
Proof.
  intros; apply substitute_vl_gt_prooforder; trivial.
Save.
Hint Immediate substitute_vl_gt : substitute.

Lemma substitute_vl_ne:
  forall (x i: nat) (u: lterm) (ul: list lterm) (d: lterm),
  x <> i -> subst_var_list x i (u :: ul) d = subst_var_list x (S i) ul d.
Proof.
  intros x i u ul d H.
  cut (x < i \/ x > i).
    intro H0; destruct H0.
    rewrite (substitute_vl_lt x i (u::ul) d); trivial.
    rewrite (substitute_vl_lt x (S i) ul d); auto with arith.
    apply (substitute_vl_gt x i u ul d); trivial.
    apply (nat_total_order x i); trivial.
Save.

Lemma substitue_vl_nth_with_diff:
  forall (n: nat) (ul: list lterm) (i: nat) (d: lterm),
  subst_var_list (i + n) i ul d = nth n ul d.
Proof.
  induction n; induction ul; intros i d; simpl.
    auto with substitute.
    rewrite <- (plus_n_O i). apply (substitute_vl_eq i a ul d).
    auto with substitute.
    rewrite (substitute_vl_gt (i + S n) i a ul d).
      rewrite <- (plus_n_Sm i n).
      rewrite <- (plus_Sn_m i n).
      apply (IHn ul (S i) d).

      rewrite <- (plus_n_Sm i n).
      apply (le_lt_n_Sm i (i + n)).
      apply (le_plus_l i n).
Save.

Lemma substitute_vl_nth:
  forall (x i: nat) (ul: list lterm) (d: lterm),
  i <= x -> subst_var_list x i ul d = nth (x - i) ul d.
Proof.
  intros x i ul d H.
  cut (x = i + (x - i)).
    intro H0; rewrite H0.
    rewrite (substitue_vl_nth_with_diff (x - i) ul i d).
    rewrite <- H0; trivial.
    auto with arith.
Save.

Lemma substitute_vl_nth_from_O:
  forall (x: nat) (ul: list lterm) (d: lterm),
  subst_var_list x O ul d = nth x ul d.
Proof.
  intros x ul d.
  rewrite (substitute_vl_nth x O ul d); auto with arith.
  cut (x = (x - O)); auto with arith.
  intro H0; rewrite H0 at 2; trivial.
Save.

Lemma substitute_vl_in:
  forall (x i: nat) (ul: list lterm) (d: lterm),
  i <= x < i + length ul -> In (subst_var_list x i ul d) ul.
Proof.
  intros x i ul d H; destruct H.
  rewrite (substitute_vl_nth x i ul d); trivial.
  apply (nth_In ul d).
  apply (plus_lt_reg_l (x - i) (length ul) i).
  rewrite <- (le_plus_minus i x); trivial.
Save.

Lemma substitute_vl_gt_overflow:
  forall (x i: nat) (ul: list lterm) (d: lterm),
  x >= i + length ul -> subst_var_list x i ul d = d.
Proof.
  intros x i ul d H.
  cut (x >= i).
    intro H0.
    rewrite (substitute_vl_nth x i ul d); trivial.
    apply (nth_overflow ul d).
    apply (plus_le_reg_l (length ul) (x - i) i).
    rewrite <- (le_plus_minus i x); trivial.
    eauto with arith.
Save.

Lemma substitute_vl_values:
  forall (x i: nat) (ul: list lterm) (d: lterm),
  subst_var_list x i ul d = d \/ In (subst_var_list x i ul d) ul.
Proof.
  intros x i ul d.
  cut (i + length ul <= x \/ x < i + length ul).
    intro H; destruct H.
      apply or_introl. apply substitute_vl_gt_overflow; trivial.
      cut (i <= x \/ x < i).
        intro H0; destruct H0.
          apply or_intror. apply substitute_vl_in; auto.
          apply or_introl. apply substitute_vl_lt; trivial.

        apply le_or_lt.
    apply le_or_lt.
Save.
