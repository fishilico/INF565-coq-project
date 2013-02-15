Require Import lterm substitution.

(** 2.1. One step of Beta-reduction *)
Inductive beta_reduct: lterm -> lterm -> Prop :=
  | Beta_reduct_step:
    forall t u: lterm, beta_reduct (Apply (Lambda t) u) (subst t 0 u)
  | Beta_reduct_close_apply1:
    forall t u v: lterm, beta_reduct t u -> beta_reduct (Apply t v) (Apply u v)
  | Beta_reduct_close_apply2:
    forall t u v: lterm, beta_reduct t u -> beta_reduct (Apply v t) (Apply v u)
  | Beta_reduct_close_lambda:
    forall t u: lterm, beta_reduct t u -> beta_reduct (Lambda t) (Lambda u)     
.

(** 2.2. Beta-reduction in any number of steps *)
Inductive beta_reduct_star: lterm -> lterm -> Prop :=
  | Beta_reduct_star_eq: forall t: lterm, beta_reduct_star t t
  | Beta_reduct_star_step: forall t u v: lterm,
      beta_reduct t u -> beta_reduct_star u v -> beta_reduct_star t v
.

(** 2.3. Prove beta_reduct properties for beta_reduct_star *)
Theorem beta_reduct_one_is_star:
  forall t u: lterm, beta_reduct t u -> beta_reduct_star t u.
Proof.
  intros t u H.
  apply (Beta_reduct_star_step t u u); trivial.
  apply Beta_reduct_star_eq.
Save.

Theorem beta_reduct_star_step:
  forall t u: lterm, beta_reduct_star (Apply (Lambda t) u) (subst t 0 u).
Proof.
  intros t u.
  apply beta_reduct_one_is_star.
  apply Beta_reduct_step.
Save.

Theorem beta_reduct_star_close_apply1:
  forall t u v: lterm,
  beta_reduct_star t u -> beta_reduct_star (Apply t v) (Apply u v).
Proof.
  intros t u v H; induction H.
  apply Beta_reduct_star_eq.
  apply (Beta_reduct_star_step (Apply t v) (Apply u v) (Apply v0 v)); trivial.
  apply Beta_reduct_close_apply1; trivial.
Save.

Theorem beta_reduct_star_close_apply2:
  forall t u v: lterm,
  beta_reduct_star t u -> beta_reduct_star (Apply v t) (Apply v u).
Proof.
  intros t u v H; induction H.
  apply Beta_reduct_star_eq.
  apply (Beta_reduct_star_step (Apply v t) (Apply v u) (Apply v v0)); trivial.
  apply Beta_reduct_close_apply2; trivial.
Save.

Theorem beta_reduct_star_close_lambda:
  forall t u: lterm,
  beta_reduct_star t u -> beta_reduct_star (Lambda t) (Lambda u).
Proof.
  intros t u H; induction H.
  apply Beta_reduct_star_eq.
  apply (Beta_reduct_star_step (Lambda t) (Lambda u) (Lambda v)); trivial.
  apply Beta_reduct_close_lambda; trivial.
Save.
