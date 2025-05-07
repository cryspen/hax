module Core.Fmt.Rt
open Rust_primitives

val t_Argument: Type0
val impl_1__new_display (#t:Type0) (x: t): t_Argument
val impl_1__new_debug (#t:Type0) (x: t): t_Argument
val impl_4__new_v1_formatted (#t:Type0) (x: t) : t_Argument
val impl_1__new_binary (#t:Type0) (x: t) : t_Argument
val impl_1__new_lower_hex (#t:Type0) (x: t) : t_Argument

val impl_1__none : unit -> t_Array Core.Fmt.Rt.t_Argument (MkInt 0)
