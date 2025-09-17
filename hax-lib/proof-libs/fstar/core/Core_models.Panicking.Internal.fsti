module Core_models.Panicking.Internal
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

val panic: #v_T: Type0 -> Prims.unit -> Prims.Pure v_T (requires false) (fun _ -> Prims.l_True)
