module Core_models.Fmt.Rt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

val t_ArgumentType:eqtype

type t_Argument = { f_ty:t_ArgumentType }

val impl__new_display (#v_T: Type0) (x: v_T)
    : Prims.Pure t_Argument Prims.l_True (fun _ -> Prims.l_True)

val impl__new_debug (#v_T: Type0) (x: v_T)
    : Prims.Pure t_Argument Prims.l_True (fun _ -> Prims.l_True)

val impl__new_lower_hex (#v_T: Type0) (x: v_T)
    : Prims.Pure t_Argument Prims.l_True (fun _ -> Prims.l_True)

val impl_1__new_binary (#v_T: Type0) (x: v_T)
    : Prims.Pure t_Argument Prims.l_True (fun _ -> Prims.l_True)

val impl_1__new_const (#v_T #v_U: Type0) (x: v_T) (y: v_U)
    : Prims.Pure Core_models.Fmt.t_Arguments Prims.l_True (fun _ -> Prims.l_True)

val impl_1__new_v1 (#v_T #v_U #v_V #v_W: Type0) (x: v_T) (y: v_U) (z: v_V) (t: v_W)
    : Prims.Pure Core_models.Fmt.t_Arguments Prims.l_True (fun _ -> Prims.l_True)

val impl_1__none: Prims.unit
  -> Prims.Pure (t_Array t_Argument (mk_usize 0)) Prims.l_True (fun _ -> Prims.l_True)

val impl_1__new_v1_formatted (#v_T #v_U #v_V: Type0) (x: v_T) (y: v_U) (z: v_V)
    : Prims.Pure Core_models.Fmt.t_Arguments Prims.l_True (fun _ -> Prims.l_True)

type t_Count =
  | Count_Is : u16 -> t_Count
  | Count_Param : u16 -> t_Count
  | Count_Implied : t_Count

type t_Placeholder = {
  f_position:usize;
  f_flags:u32;
  f_precision:t_Count;
  f_width:t_Count
}

type t_UnsafeArg = | UnsafeArg : t_UnsafeArg
