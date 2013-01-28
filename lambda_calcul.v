Require Import List.
Load Arith_ext.

(******* PART 1 *******)

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
    | Lambda u => freevars_below (S n) u
    | Apply u v => (freevars_below n u) /\ (freevars_below n v)
  end
.

(* Closed term *)
Definition closed (t: lterm) : Prop :=
  freevars_below 0 t
.

(* freevars_below is still True when n increases *)
Theorem freevars_below_S:
  forall (t: lterm) (n: nat),
  freevars_below n t -> freevars_below (S n) t.
Proof.
  induction t; simpl.
    intros n0 H. apply lt_S. trivial.
    intros n H. apply (IHt (S n)). trivial.
    intros n H. apply conj.
      apply IHt1. apply H.
      apply IHt2. apply H.
Save.
Theorem freevars_below_incr:
  forall (t: lterm) (n m: nat),
  freevars_below n t /\ n <= m -> freevars_below m t.
Proof.
  intros t n; induction m; intro H; destruct H.
    cut (O = n).
      intro H1. rewrite H1. trivial.
      apply (le_n_0_eq n). trivial.

    cut (n < S m \/ n = S m). (*(n = S m) \/ (n <= m)*)
      intro H1. destruct H1.
        apply (freevars_below_S t m). apply IHm.
        apply conj. trivial. apply (lt_n_Sm_le n m). trivial.

        rewrite <- H1. trivial.
      apply (le_lt_or_eq n (S m)). trivial.
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
    | Lambda t0 => Lambda (substitute t0 (S x) u)
    | Apply t0 u0 => Apply (substitute t0 x u) (substitute u0 x u)
  end
.

(* Substitution on a free variable does nothing *)
Lemma substitute_freevars_eq:
  forall (t: lterm) (n: nat) (x: nat) (u: lterm),
  ((freevars_below n t) /\ (x >= n)) -> (substitute t x u) = t.
Proof.
  induction t.
    intros n0 x u H. simpl.
    destruct H.
    assert (beq_nat x n = false).
      rewrite (beq_nat_false_iff x n).
      apply lt_neq_sym.
      apply (lt_le_trans n n0 x); trivial.
    rewrite H1. trivial.

    intros n x u H. simpl. 
    rewrite (IHt (S n) (S x) u); trivial.
    apply conj. apply H. apply (le_n_S n x). apply H.

    intros n x u H. simpl. 
    rewrite (IHt1 n x u). rewrite (IHt2 n x u). trivial.
    apply conj; apply H.
    apply conj; apply H.
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

(* Substitution of variable x in a list i->u0, i+1->u1, i+2->u2, ...
 * Return d by default
 *)
Fixpoint substitute_var_list (x i: nat) (ul: list lterm) (d: lterm) : lterm :=
  match ul, i, x with
    | nil, _, _ => d
    | t :: _, O, O => t
    | _ :: vl, O, S y => substitute_var_list y O vl d
    | _ :: _, S _, O => d
    | _ :: _, S j, S y => substitute_var_list y j ul d
  end
.

(* Substitution with a list of terms i->u0, i+1->u1, i+2->u2, ... *)
Fixpoint substitute_list (t: lterm) (i: nat) (u: list lterm) : lterm :=
  match t with
    | Var x =>  substitute_var_list x i u (Var x)
    | Lambda t0 => Lambda (substitute_list t0 (S i) u)
    | Apply t0 u0 => Apply (substitute_list t0 i u) (substitute_list u0 i u)
  end
.
Theorem substitute_list_empty:
  forall (t: lterm) (i: nat), substitute_list t i nil = t.
Proof.
  induction t; intro i; simpl.
    induction n; induction i; trivial.
    rewrite (IHt (S i)). trivial.
    rewrite IHt1; rewrite IHt2. trivial.
Save.

Lemma substitute_var_list_eq:
  (* i = n + a + 1 *)
  forall (n a: nat) (ul: list lterm) (d: lterm),
    substitute_var_list n (n + 1 + a) ul d = d.
Proof.
  induction n; induction a; induction ul; intro d; simpl; trivial.
Save.

Theorem substitute_singlelist_free_eq:
  forall (t: lterm) (i: nat) (u: lterm),
  freevars_below i t -> substitute_list t i (u :: nil) = t.
Proof.
  induction t; simpl; intros i u H; simpl.
    rewrite (le_plus_minus (n + 1) i).
    rewrite (minus_plus_simpl i n 1).
    apply (substitute_var_list_eq n (i - n - 1) (u :: nil) (Var n)).
    rewrite <- (plus_n_Sm n O).
    rewrite <- (plus_n_O n).
    apply (lt_le_S n i).
    trivial.

    rewrite (IHt (S i) u); trivial.

    destruct H.
    rewrite (IHt1 i u); trivial.
    rewrite (IHt2 i u); trivial.
Save.
