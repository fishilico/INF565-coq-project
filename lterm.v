(* Lambda term with De Bruijn indexes *)
Inductive lterm : Set :=
  | Var: nat -> lterm
  | Lambda: lterm -> lterm
  | Apply: lterm -> lterm -> lterm
.

(* Example of function: the identity *)
Definition l_id: lterm := Lambda (Var O)
.
