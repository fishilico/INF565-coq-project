(** 1.1. Lambda term with De Bruijn indexes *)
Inductive lterm : Set :=
  | Var: nat -> lterm
  | Lambda: lterm -> lterm
  | Apply: lterm -> lterm -> lterm
.
