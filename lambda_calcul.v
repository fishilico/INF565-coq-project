Load Arith_ext.

(* Lambda term with De Bruijn indexes *)
Inductive lterm : Set :=
  | Var: nat -> lterm
  | Lambda: lterm -> lterm
  | Apply: lterm -> lterm -> lterm
.

(* Example of function: the identity *)
Definition l_id: lterm := Lambda (Var 0)
.

(* Predicate: every free variable has an index below n *)
Fixpoint freevars_below (n: nat) (t: lterm) : Prop :=
  match t with
    | Var x => x < n
    | Lambda u => freevars_below (n + 1) u
    | Apply u v => (freevars_below n u) /\ (freevars_below n v)
  end
.

(* Closed term *)
Definition closed (t: lterm) : Prop :=
  freevars_below 0 t
.

(* freevars_below is still True when n increases *)
Lemma freevars_below_incr:
  forall (t: lterm) (n m: nat),
  freevars_below n t /\ n <= m -> freevars_below m t.
Proof.
  induction t.
    intros n0 m H. simpl.
    apply (lt_le_trans n n0 m). apply H. apply H.

    intros n m H. simpl.
    apply (IHt (n + 1) (m + 1)). apply conj. apply H.
    destruct H. apply (plus_le_compat_r n m 1). trivial.

    intros n m H. simpl.
    apply conj.
    apply (IHt1 n m). apply conj. apply H. apply H.
    apply (IHt2 n m). apply conj. apply H. apply H.
Save.

(*
 * Substitute x with u in t, ie. return t[x <- u]
 *
 * (Var 0)[0 <- u] = u
 * (Var 1)[0 <- u] = Var 1
 * (Lambda t)[0 <- u] = Lambda (t[1 <- u])
 *)
Fixpoint substitute (t: lterm) (x: nat) (u: lterm) : lterm :=
  match t with
    | Var y => if beq_nat x y then u else t
    | Lambda t0 => Lambda (substitute t0 (x+1) u)
    | Apply t0 u0 => Apply (substitute t0 x u) (substitute u0 x u)
  end
.

(* Substitution on a free variable does nothing *)
Lemma substitute_freevars_eq:
  forall (t: lterm) (n: nat) (x: nat) (u: lterm),
  ((freevars_below n t) /\ (x >= n)) -> (substitute t x u) = t.
Proof.
  induction t.
    intros n0 x u H.
    unfold substitute.
    destruct H.
    assert (beq_nat x n = false).
      rewrite (beq_nat_false_iff x n).
      apply lt_neq. apply or_intror.
      apply (lt_le_trans n n0 x). apply H. apply H0.
    rewrite H1. trivial.

    intros n x u H. simpl. 
    rewrite (IHt (n + 1) (x + 1) u). trivial.
    apply conj. apply H. apply (plus_le_compat_r n x 1). apply H.

    intros n x u H. simpl. 
    rewrite (IHt1 n x u). rewrite (IHt2 n x u). trivial.
    apply conj. apply H. apply H.
    apply conj. apply H. apply H.
Save.

(* Substitution on a closed term does nothing *)
Theorem substitute_closed_eq:
  forall (t: lterm) (x: nat) (u: lterm), closed t -> (substitute t x u) = t.
Proof.
  intros t x u H.
  apply (substitute_freevars_eq t 0 x u).
  apply conj.
  apply H.
  apply le_0_n.
Save.
