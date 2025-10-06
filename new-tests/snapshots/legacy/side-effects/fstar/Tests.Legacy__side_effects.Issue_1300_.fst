module Tests.Legacy__side_effects.Issue_1300_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_fun (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  match
    Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8)
          (u8 -> Core.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8))
      #FStar.Tactics.Typeclasses.solve
      #(Core.Result.t_Result (Alloc.Vec.t_Vec (u8 & t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global)
          u8)
      (Core.Iter.Traits.Iterator.f_map #(Core.Slice.Iter.t_Iter u8)
          #FStar.Tactics.Typeclasses.solve
          #(Core.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8)
          (Core.Slice.impl__iter #u8
              (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 5) <: t_Slice u8)
            <:
            Core.Slice.Iter.t_Iter u8)
          (fun prev ->
              let prev:u8 = prev in
              match
                Core.Result.Result_Ok
                (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) <: t_Array u8 (mk_usize 32))
                <:
                Core.Result.t_Result (t_Array u8 (mk_usize 32)) u8
              with
              | Core.Result.Result_Ok hoist45 ->
                Core.Result.Result_Ok (prev, hoist45 <: (u8 & t_Array u8 (mk_usize 32)))
                <:
                Core.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8)
        <:
        Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8)
          (u8 -> Core.Result.t_Result (u8 & t_Array u8 (mk_usize 32)) u8))
    <:
    Core.Result.t_Result (Alloc.Vec.t_Vec (u8 & t_Array u8 (mk_usize 32)) Alloc.Alloc.t_Global) u8
  with
  | Core.Result.Result_Ok v_val ->
    Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8
