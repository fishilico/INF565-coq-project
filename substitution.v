Require Import Arith_ext free_variables lterm.

(**
 * Substitute x with u in t, ie. return t[x <- u]
 *
 * (Var 0)[0 <- u] = u
 * (Var 1)[0 <- u] = Var 1
 * (Lambda t)[0 <- u] = Lambda (t[1 <- u])
 *)
Fixpoint subst (t: lterm) (x: nat) (u: lterm) : lterm :=
  match t with
    | Var y => if beq_nat x y then u else t
    | Lambda t0 => Lambda (subst t0 (S x) u)
    | Apply t0 u0 => Apply (subst t0 x u) (subst u0 x u)
  end
.

(** Substitution on a free variable does nothing *)
Lemma substitute_freevar_eq:
  forall (t: lterm) (x: nat) (u: lterm), fr_below x t -> subst t x u = t.
Proof.
  induction t; simpl; intros x u H.
    assert (beq_nat x n = false).
      rewrite (beq_nat_false_iff x n).
      apply lt_neq_sym; trivial.
    rewrite H0; trivial.

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
