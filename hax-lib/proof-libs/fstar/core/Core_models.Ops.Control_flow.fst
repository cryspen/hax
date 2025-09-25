module Core_models.Ops.Control_flow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

type t_ControlFlow (v_B: Type0) (v_C: Type0) =
  | ControlFlow_Continue : v_C -> t_ControlFlow v_B v_C
  | ControlFlow_Break : v_B -> t_ControlFlow v_B v_C
