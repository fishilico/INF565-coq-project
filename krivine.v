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

(** a state is (code, env, stack) tuple which may be seen as an environment *)
Definition krivine_state (c: krivine_code) (e s: krivine_env) : krivine_env :=
  KEnv c e s
.

(** Length of an environment list *)
Fixpoint klength (e: krivine_env) : nat :=
  match e with
    | KEnv_nil => O
    | KEnv _ _ e0 => S (klength e0)
  end
.

(** 3.3. Semantic: execute one step.
  Return KEnv_nil if there were some error, a krivine_state otherwise.
 *)
Definition krivine_step (st: krivine_env) : krivine_env :=
  match st with
    | KEnv (Access O _) (KEnv c0 e0 _) s => krivine_state c0 e0 s
    | KEnv (Access (S n) c) (KEnv _ _ e) s =>
        krivine_state (Access n c) e s
    | KEnv (Push c0 c) e s => krivine_state c e (KEnv c0 e s)
    | KEnv (Grab c) e (KEnv c0 e0 s) =>
        krivine_state c (KEnv c0 e0 e) s
    | _ => KEnv_nil
  end
.
