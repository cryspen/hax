module Core.Fmt
open Rust_primitives
module Rt = Core.Fmt.Rt

val t_Error: Type0

type t_Result = Core.Result.t_Result unit t_Error

val t_Formatter: Type0
class t_Display t_Self = {
  f_fmt_pre: t_Self -> t_Formatter -> bool;
  f_fmt_post: t_Self -> t_Formatter -> (t_Formatter & Core.Result.t_Result Prims.unit t_Error) -> bool;
  f_fmt: t_Self -> t_Formatter -> (t_Formatter & Core.Result.t_Result Prims.unit t_Error)
}

class t_Debug t_Self = {
  f_dbg_fmt_pre: t_Self -> Core.Fmt.t_Formatter -> bool;
  f_dbg_fmt_post: t_Self -> Core.Fmt.t_Formatter -> (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) -> bool;
  f_dbg_fmt: t_Self -> Core.Fmt.t_Formatter -> (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
}

let t_Arguments = Rt.t_Argument
val impl_4__new_v1 (sz1: usize) (sz2: usize) (pieces: t_Slice string) (args: t_Slice Core.Fmt.Rt.t_Argument): t_Arguments
val impl_7__write_fmt (fmt: t_Formatter) (args: t_Arguments): t_Formatter & t_Result
val impl_4__new_const (u:usize) (args: t_Slice string): t_Arguments
val impl_4__new_v1_formatted :
   pieces: t_Slice string ->
	 args: t_Slice Rt.t_Argument ->
	 fmt: t_Slice Rt.t_Placeholder ->
	 unsafe_arg: Rt.t_UnsafeArg ->
	 t_Arguments

val impl_11__write_fmt : Core.Fmt.t_Formatter -> Core.Fmt.t_Arguments -> Core.Fmt.t_Formatter & Core.Result_Option_bundle.t_Result unit Core.Fmt.t_Error

instance debuggable_bool : t_Debug Prims.bool =
{
  f_dbg_fmt_pre = (fun (b: Prims.bool) (fmt: Core.Fmt.t_Formatter) -> true);
  f_dbg_fmt_post = (fun (b: Prims.bool) (fmt: Core.Fmt.t_Formatter) (result: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)) -> true);
  f_dbg_fmt = (fun (b: Prims.bool) (fmt: Core.Fmt.t_Formatter) -> (fmt, Core.Result.Result_Ok ()));
}

instance debuggable_u128 : t_Debug Rust_primitives.Integers.u128 =
{
  f_dbg_fmt_pre = (fun (b: Rust_primitives.Integers.u128) (fmt: Core.Fmt.t_Formatter) -> true);
  f_dbg_fmt_post = (fun (b: Rust_primitives.Integers.u128) (fmt: Core.Fmt.t_Formatter) (result: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)) -> true);
  f_dbg_fmt = (fun (b: Rust_primitives.Integers.u128) (fmt: Core.Fmt.t_Formatter) -> (fmt, Core.Result.Result_Ok ()));
}

instance debuggable_pair (#a:Type) (#b:Type) (x: t_Debug a) (y: t_Debug b): t_Debug (a & b) =
{
  f_dbg_fmt_pre = (fun (pair: (a & b)) (fmt: Core.Fmt.t_Formatter) -> f_dbg_fmt_pre pair._1 fmt && f_dbg_fmt_pre pair._2 fmt);
  f_dbg_fmt_post = (fun (pair: (a & b)) (fmt: Core.Fmt.t_Formatter) (result: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)) -> f_dbg_fmt_post pair._1 fmt result && f_dbg_fmt_post pair._2 fmt result);
  f_dbg_fmt = (fun (pair: (a & b)) (fmt: Core.Fmt.t_Formatter) ->
     let fmt_a, result_a:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) = f_dbg_fmt pair._1 fmt in
     match result_a with
     | Core.Result.Result_Ok v -> f_dbg_fmt pair._2 fmt_a
     | Core.Result.Result_Err e -> (fmt_a, result_a));
}
