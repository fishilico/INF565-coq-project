Require Import Arith_ext free_variables List lterm substitute_varlist.

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
  induction t; simpl; intros ul i u H.
    cut (n = i \/ n <> i).
      intro H0; destruct H0.
        (* n = i *)
        rewrite <- H0.
        rewrite (substitute_vl_eq n u ul (Var n)).
        rewrite (substitute_vl_lt n (S n) ul (Var n)); auto with arith.
        simpl.
        auto with substitute.
        (* n <> i *)
        rewrite (substitute_vl_ne n i u ul (Var n)); trivial.
        cut (subst_var_list n (S i) ul (Var n) = Var n \/
             In (subst_var_list n (S i) ul (Var n)) ul).
          intro H1; destruct H1.
            (* subst_var_list n (S i) ul (Var n) = Var n *)
            rewrite H1; simpl.
            rewrite substitute_vl_ne; trivial.
            rewrite substitute_vl_nil; trivial.
            (* In (subst_var_list n (S i) ul (Var n)) ul *)
            rewrite (substitute_singlelist_free_eq
                     (subst_var_list n (S i) ul (Var n)) i u); trivial.
            apply (fr_below_list_forall i ul); trivial.
          apply (substitute_vl_values n (S i) ul (Var n)).
      apply neq_or_eq.

    (* Lambda *)
    rewrite IHt; trivial.
    apply fr_below_list_S; trivial.

    (* Apply *)
    rewrite IHt1; trivial.
    rewrite IHt2; trivial.
Save.
