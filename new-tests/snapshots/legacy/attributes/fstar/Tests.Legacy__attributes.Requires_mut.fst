module Tests.Legacy__attributes.Requires_mut
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Foo (v_Self: Type0) = {
  f_f_pre:x: u8 -> y: u8
    -> pred:
      Type0
        { ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int) <
          (254 <: Hax_lib.Int.t_Int) ==>
          pred };
  f_f_post:x: u8 -> y: u8 -> x1: (u8 & u8)
    -> pred:
      Type0
        { pred ==>
          (let y_future, output_variable:(u8 & u8) = x1 in
            output_variable =. y_future) };
  f_f:x0: u8 -> x1: u8 -> Prims.Pure (u8 & u8) (f_f_pre x0 x1) (fun result -> f_f_post x0 x1 result);
  f_g_pre:u8 -> u8 -> Type0;
  f_g_post:u8 -> u8 -> u8 -> Type0;
  f_g:x0: u8 -> x1: u8 -> Prims.Pure u8 (f_g_pre x0 x1) (fun result -> f_g_post x0 x1 result);
  f_h_pre:u8 -> u8 -> Type0;
  f_h_post:u8 -> u8 -> Prims.unit -> Type0;
  f_h:x0: u8 -> x1: u8
    -> Prims.Pure Prims.unit (f_h_pre x0 x1) (fun result -> f_h_post x0 x1 result);
  f_i_pre:u8 -> u8 -> Type0;
  f_i_post:u8 -> u8 -> u8 -> Type0;
  f_i:x0: u8 -> x1: u8 -> Prims.Pure u8 (f_i_pre x0 x1) (fun result -> f_i_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Foo Prims.unit =
  {
    f_f_pre
    =
    (fun (x: u8) (y: u8) ->
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <
        (254 <: Hax_lib.Int.t_Int));
    f_f_post
    =
    (fun (x: u8) (y: u8) (y_future, output_variable: (u8 & u8)) -> output_variable =. y_future);
    f_f
    =
    (fun (x: u8) (y: u8) ->
        let y:u8 = y +! x in
        let hax_temp_output:u8 = y in
        y, hax_temp_output <: (u8 & u8));
    f_g_pre = (fun (x: u8) (y: u8) -> true);
    f_g_post = (fun (x: u8) (y: u8) (output_variable: u8) -> output_variable =. y);
    f_g = (fun (x: u8) (y: u8) -> y);
    f_h_pre = (fun (x: u8) (y: u8) -> true);
    f_h_post
    =
    (fun (x: u8) (y: u8) (output_variable: Prims.unit) -> output_variable =. (() <: Prims.unit));
    f_h = (fun (x: u8) (y: u8) -> () <: Prims.unit);
    f_i_pre = (fun (x: u8) (y: u8) -> true);
    f_i_post = (fun (x: u8) (y: u8) (y_future: u8) -> y_future =. y);
    f_i
    =
    fun (x: u8) (y: u8) ->
      let _:Prims.unit = () <: Prims.unit in
      y
  }
