module Tests.Legacy__traits.For_clauses.Issue_495_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let original_function_from_495_ (list: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Prims.unit =
  let (e_indices: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Filter.t_Filter
          (Core.Ops.Range.t_Range u8) (u8 -> bool))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      (Core.Iter.Traits.Iterator.f_filter #(Core.Ops.Range.t_Range u8)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = mk_u8 0; Core.Ops.Range.f_end = mk_u8 5 }
            <:
            Core.Ops.Range.t_Range u8)
          (fun i ->
              let i:u8 = i in
              let _, out:(Core.Slice.Iter.t_Iter u8 & bool) =
                Core.Iter.Traits.Iterator.f_any #(Core.Slice.Iter.t_Iter u8)
                  #FStar.Tactics.Typeclasses.solve
                  (Core.Slice.impl__iter #u8
                      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                          #FStar.Tactics.Typeclasses.solve
                          list
                        <:
                        t_Slice u8)
                    <:
                    Core.Slice.Iter.t_Iter u8)
                  (fun n ->
                      let n:u8 = n in
                      n =. i <: bool)
              in
              out)
        <:
        Core.Iter.Adapters.Filter.t_Filter (Core.Ops.Range.t_Range u8) (u8 -> bool))
  in
  ()

let minimized_1_ (list: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Filter.t_Filter
        (Core.Ops.Range.t_Range u8) (u8 -> bool))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    (Core.Iter.Traits.Iterator.f_filter #(Core.Ops.Range.t_Range u8)
        #FStar.Tactics.Typeclasses.solve
        ({ Core.Ops.Range.f_start = mk_u8 0; Core.Ops.Range.f_end = mk_u8 5 }
          <:
          Core.Ops.Range.t_Range u8)
        (fun temp_0_ ->
            let _:u8 = temp_0_ in
            true)
      <:
      Core.Iter.Adapters.Filter.t_Filter (Core.Ops.Range.t_Range u8) (u8 -> bool))

let minimized_2_ (it: Core.Iter.Adapters.Filter.t_Filter (Core.Ops.Range.t_Range u8) (u8 -> bool))
    : Prims.unit =
  let (e_indices: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Filter.t_Filter
          (Core.Ops.Range.t_Range u8) (u8 -> bool))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      it
  in
  ()
