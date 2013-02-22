(** 3. Krivine Abstract Machine *)
Require Import List.

(** 3.2. Krivine code
Code is a list of Access, Grab and Push instructions. This definition merge
instruction and "code = list instruction" definitions, to allow recursion
on Push parameter.
To do this, add "Nop" code, which is equivalent to the nil list.
*)
Inductive krivine_code : Set :=
  | Nop: krivine_code
  | Access: nat -> krivine_code -> krivine_code
  | Grab: krivine_code -> krivine_code
  | Push: krivine_code -> krivine_code -> krivine_code
.

(** Environment stack : (c, e) list *)
Inductive krivine_env : Set :=
  | KEnv_nil: krivine_env
  | KEnv: krivine_code -> krivine_env -> krivine_env -> krivine_env
.

(* State *)
Inductive krivine_state : Set :=
  | KState: krivine_code -> krivine_env -> krivine_env -> krivine_state.

(** 3.3. Semantic: execute one step *)
Definition krivine_step (st: krivine_state) : option krivine_state :=
  match st with
    | KState (Access O _) (KEnv c0 e0 _) s => Some (KState c0 e0 s)
    | KState (Access (S n) c) (KEnv _ _ e) s =>
        Some (KState (Access n c) e s)
    | KState (Push c0 c) e s => Some (KState c e (KEnv c0 e s))
    | KState (Grab c) e (KEnv c0 e0 s) =>
        Some (KState c (KEnv c0 e0 e) s)
    | _ => None
  end
.
