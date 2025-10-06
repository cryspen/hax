module Tests.Legacy__side_effects.Issue_1083_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_MyFrom (v_Self: Type0) (v_T: Type0) = {
  f_my_from_pre:v_T -> Type0;
  f_my_from_post:v_T -> v_Self -> Type0;
  f_my_from:x0: v_T -> Prims.Pure v_Self (f_my_from_pre x0) (fun result -> f_my_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_MyFrom u16 u8 =
  {
    f_my_from_pre = (fun (x: u8) -> true);
    f_my_from_post = (fun (x: u8) (out: u16) -> true);
    f_my_from = fun (x: u8) -> cast (x <: u8) <: u16
  }

let f (x: u8) : Core.Result.t_Result u16 u16 =
  match
    Core.Ops.Try_trait.f_branch #(Core.Result.t_Result Rust_primitives.Hax.t_Never u8)
      #FStar.Tactics.Typeclasses.solve
      (Core.Result.Result_Err (mk_u8 1) <: Core.Result.t_Result Rust_primitives.Hax.t_Never u8)
    <:
    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Core.Convert.t_Infallible u8)
      Rust_primitives.Hax.t_Never
  with
  | Core.Ops.Control_flow.ControlFlow_Break residual ->
    Core.Ops.Try_trait.f_from_residual #(Core.Result.t_Result u16 u16)
      #(Core.Result.t_Result Core.Convert.t_Infallible u8)
      #FStar.Tactics.Typeclasses.solve
      residual
  | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
    let _:Rust_primitives.Hax.t_Never = v_val in
    Core.Result.Result_Ok (f_my_from #u16 #u8 #FStar.Tactics.Typeclasses.solve x)
    <:
    Core.Result.t_Result u16 u16
