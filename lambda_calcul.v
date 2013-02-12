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

(*
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

(* Substitution on a free variable does nothing *)
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

(* Substitution on a closed term does nothing *)
Theorem substitute_closed_eq:
  forall (t: lterm) (x: nat) (u: lterm), closed t -> subst t x u = t.
Proof.
  intros t x u H.
  apply (substitute_freevar_eq t x u).
  apply (fr_below_incr t 0 x).
  apply conj.
    apply H.
    apply le_0_n.
Save.

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

(* Substitution with a list of terms i->u0, i+1->u1, i+2->u2, ... *)
Fixpoint subst_list (t: lterm) (i: nat) (u: list lterm) : lterm :=
  match t with
    | Var x =>  subst_var_list x i u (Var x)
    | Lambda t0 => Lambda (subst_list t0 (S i) u)
    | Apply t0 u0 => Apply (subst_list t0 i u) (subst_list u0 i u)
  end
.

Theorem substitute_list_empty:
  forall (t: lterm) (i: nat), subst_list t i nil = t.
Proof.
  induction t; intro i; simpl.
    induction n; induction i; trivial.
    rewrite (IHt (S i)); trivial.
    rewrite IHt1; rewrite IHt2; trivial.
Save.

Theorem substitute_singlelist_free_eq:
  forall (t: lterm) (i: nat) (u: lterm),
  fr_below i t -> subst_list t i (u :: nil) = t.
Proof.
  induction t; simpl; intros i u H; simpl.
    auto with substitute.
    rewrite (IHt (S i) u); trivial.
    destruct H.
    rewrite (IHt1 i u); trivial.
    rewrite (IHt2 i u); trivial.
Save.


Theorem substitute_list_cons_free_eq:
  forall (t: lterm) (ul: list lterm) (i: nat) (u: lterm),
  fr_below_list i ul ->
    subst_list t i (u :: ul) = subst_list (subst_list t (S i) ul) i (u :: nil).
Proof.
  induction t; simpl.
    induction ul; simpl; intros i u H.
      induction i; induction n; trivial.
      destruct H.
      cut (n = i \/ n <> i).
        intro H1; destruct H1.
          (* n = i *)
          rewrite <- H1.
          rewrite (substitute_vl_eq n u (a :: ul) (Var n)).
          rewrite (substitute_vl_lt n (S n) (a :: ul) (Var n)); auto with arith.
          simpl.
          auto with substitute.
          (* n <> i *)
          rewrite (substitute_vl_ne n i u (a :: ul) (Var n)); trivial.
          cut (subst_var_list n (S i) (a :: ul) (Var n) = Var n \/
               In (subst_var_list n (S i) (a :: ul) (Var n)) (a :: ul)).
            intro H2; destruct H2.
              rewrite H2; simpl.
              rewrite substitute_vl_ne; trivial.
              rewrite substitute_vl_nil; trivial.

              rewrite (substitute_singlelist_free_eq
                       (subst_var_list n (S i) (a :: ul) (Var n)) i u); trivial.

              cut (a = subst_var_list n (S i) (a :: ul) (Var n) \/
                   In (subst_var_list n (S i) (a :: ul) (Var n)) ul).
                intro H3; destruct H3.
                  rewrite <- H3; trivial.
                  apply (fr_below_list_forall i ul); trivial.
                apply in_inv; trivial.

            apply (substitute_vl_values n (S i) (a :: ul) (Var n)).
        apply neq_or_eq.

    (* Lambda *)
    intros ul i u H.
      rewrite IHt; trivial.
      apply fr_below_list_S; trivial.

    (* Apply *)
    intros ul i u H.
      rewrite IHt1; trivial.
      rewrite IHt2; trivial.
Save.

