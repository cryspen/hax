module Coverage.Drop_trait
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Firework = { f_strength:i32 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Drop.t_Drop t_Firework =
  {
    f_drop_pre = (fun (self: t_Firework) -> true);
    f_drop_post = (fun (self: t_Firework) (out: t_Firework) -> true);
    f_drop
    =
    fun (self: t_Firework) ->
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = ["BOOM times "; "!!!\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              (let list =
                  [Core.Fmt.Rt.impl__new_display #i32 self.f_strength <: Core.Fmt.Rt.t_Argument]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      self
  }

let main (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  let e_firecracker:t_Firework = { f_strength = mk_i32 1 } <: t_Firework in
  let e_tnt:t_Firework = { f_strength = mk_i32 100 } <: t_Firework in
  if true
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["Exiting with error...\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    Core.Result.Result_Err (mk_u8 1) <: Core.Result.t_Result Prims.unit u8
  else
    let _:t_Firework = { f_strength = mk_i32 1000 } <: t_Firework in
    Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
