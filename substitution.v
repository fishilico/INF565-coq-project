Require Import Arith free_variables lterm.

(** Substitute a variable, (Var n)[x <- u], d = Var n before recursion *)
Fixpoint subst_var (n x: nat) (u d: lterm) : lterm :=
  match n, x with
    | O, O => u
    | O, S _ => d
    | S _, O => d
    | S m, S y => subst_var m y u d
  end
.

Lemma subst_var_eq:
  forall (n: nat) (u d: lterm), subst_var n n u d = u.
Proof.
  induction n; intros u d; simpl; trivial.
Save.

Lemma subst_var_lt_diff:
  forall (y n: nat) (u d: lterm), subst_var n (n + S y) u d = d.
Proof.
  induction y; induction n; intros u d; simpl; trivial.
Save.

Lemma subst_var_lt:
  forall (n x: nat) (u d: lterm), n < x -> subst_var n x u d = d.
Proof.
  intros n x u d H.
  cut (x = n + S (pred (x - n))).
    intro Hx. rewrite Hx. apply subst_var_lt_diff.
  elim (S_pred (x - n) O). auto with arith.
  apply (plus_lt_reg_l O (x - n) n).
  rewrite (plus_comm n O).
  rewrite <- (le_plus_minus n x); auto with arith.
Save.

Lemma subst_var_gt_diff:
  forall (y n: nat) (u d: lterm), subst_var (n + S y) n u d = d.
Proof.
  induction y; induction n; intros u d; simpl; trivial.
Save.

Lemma subst_var_gt:
  forall (n x: nat) (u d: lterm), n > x -> subst_var n x u d = d.
Proof.
  intros n x u d H.
  cut (n = x + S (pred (n - x))).
    intro Hx. rewrite Hx. apply subst_var_gt_diff.
  elim (S_pred (n - x) O). auto with arith.
  apply (plus_lt_reg_l O (n - x) x).
  rewrite (plus_comm x O).
  rewrite <- (le_plus_minus x n); auto with arith.
Save.


(**
 * Substitute x with u in t, ie. return t[x <- u]
 *
 * (Var 0)[0 <- u] = u
 * (Var 1)[0 <- u] = Var 1
 * (Lambda t)[0 <- u] = Lambda (t[1 <- u])
 *)
Fixpoint subst (t: lterm) (x: nat) (u: lterm) : lterm :=
  match t with
    | Var n => subst_var n x u (Var n)
    | Lambda t0 => Lambda (subst t0 (S x) u)
    | Apply t0 u0 => Apply (subst t0 x u) (subst u0 x u)
  end
.

(** Substitution on a free variable does nothing *)
Lemma substitute_freevar_eq:
  forall (t: lterm) (x: nat) (u: lterm), fr_below x t -> subst t x u = t.
Proof.
  induction t; simpl; intros x u H.
    apply subst_var_lt; trivial.
    rewrite (IHt (S x) u); trivial.
    destruct H.
      rewrite (IHt1 x u); trivial.
      rewrite (IHt2 x u); trivial.
Save.

(** Substitution on a closed term does nothing *)
Theorem substitute_closed_eq:
  forall (t: lterm) (x: nat) (u: lterm), closed t -> subst t x u = t.
Proof.
  intros t x u H.
  apply (substitute_freevar_eq t x u).
  apply (fr_below_incr t 0 x); trivial.
  auto with arith.
Save.
