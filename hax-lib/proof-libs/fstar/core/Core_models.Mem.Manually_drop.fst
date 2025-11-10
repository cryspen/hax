module Core_models.Mem.Manually_drop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

type t_ManuallyDrop (v_T: Type0) = { f_value:v_T }
