module Coverage.Generics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Firework
  (v_T: Type0) {| i0: Core_models.Marker.t_Copy v_T |} {| i1: Core_models.Fmt.t_Display v_T |}
  = { f_strength:v_T }

let impl__set_strength
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Fmt.t_Display v_T)
      (self: t_Firework v_T)
      (new_strength: v_T)
    : t_Firework v_T =
  let self:t_Firework v_T = { self with f_strength = new_strength } <: t_Firework v_T in
  self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Fmt.t_Display v_T)
    : Core_models.Ops.Drop.t_Drop (t_Firework v_T) =
  {
    f_drop_pre = (fun (self: t_Firework v_T) -> true);
    f_drop_post = (fun (self: t_Firework v_T) (out: t_Firework v_T) -> true);
    f_drop
    =
    fun (self: t_Firework v_T) ->
      let args:v_T = self.f_strength <: v_T in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_display #v_T args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = ["BOOM times "; "!!!\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      self
  }

let main (_: Prims.unit) : Core_models.Result.t_Result Prims.unit u8 =
  let firecracker:t_Firework i32 = { f_strength = mk_i32 1 } <: t_Firework i32 in
  let firecracker:t_Firework i32 = impl__set_strength #i32 firecracker (mk_i32 2) in
  let tnt:t_Firework float = { f_strength = mk_float "100.1" } <: t_Firework float in
  let tnt:t_Firework float = impl__set_strength #float tnt (mk_float "200.1") in
  let tnt:t_Firework float = impl__set_strength #float tnt (mk_float "300.3") in
  if true
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
            (let list = ["Exiting with error...\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core_models.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    Core_models.Result.Result_Err (mk_u8 1) <: Core_models.Result.t_Result Prims.unit u8
  else
    let _:t_Firework i32 = { f_strength = mk_i32 1000 } <: t_Firework i32 in
    Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
