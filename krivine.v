(** 3. Krivine Abstract Machine *)
Require Import List.

(** 3.2. Krivine instruction *)
Inductive krivine_instr : Set :=
  | Access: nat -> krivine_instr
  | Grab: krivine_instr
  | Push: list krivine_instr -> krivine_instr
.

Definition krivine_code := list krivine_instr.

(** Environment stack *)
Inductive krivine_env_item : Set :=
  | Item: krivine_code -> list krivine_env_item -> krivine_env_item
.

Definition krivine_env := list krivine_env_item.

(* State *)
Inductive krivine_state : Set :=
  | State: krivine_code -> krivine_env -> krivine_env -> krivine_state.

(** 3.3. Semantic: execute one step *)
Definition krivine_step (st: krivine_state) : option krivine_state :=
  match st with
    | State (Access O :: _) (Item c0 e0 :: _) s => Some (State c0 e0 s)
    | State (Access (S n) :: c) (Item _ _ :: e) s =>
        Some (State (Access n :: c) e s)
    | State (Push c0 :: c) e s => Some (State c e (Item c0 e :: s))
    | State (Grab :: c) e (Item c0 e0 :: s) =>
        Some (State c (Item c0 e0 :: e) s)
    | _ => None
  end
.
