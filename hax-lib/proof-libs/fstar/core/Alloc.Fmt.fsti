module Alloc.Fmt
open Rust_primitives

include Core_models.Fmt

val impl_1__new_v1 (sz1:usize) (sz2: usize) (pieces: t_Slice string) (args: Core_models.Fmt.Rt.t_Argument): t_Arguments
val impl_7__write_fmt (fmt: t_Formatter) (args: t_Arguments): Core_models.Result.t_Result unit Core_models.Fmt.t_Error

val format (args: t_Arguments): string



