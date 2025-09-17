module Core_models.Hint
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val black_box (#v_T: Type0) (dummy: v_T) : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val must_use (#v_T: Type0) (value: v_T) : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)
