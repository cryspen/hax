module Tests.Legacy__loops.For_loops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// @fail(extraction): proverif(HAX0008)
let range1 (_: Prims.unit) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 15)
      (fun acc temp_1_ ->
          let acc:usize = acc in
          let _:usize = temp_1_ in
          true)
      acc
      (fun acc i ->
          let acc:usize = acc in
          let i:usize = i in
          acc +! i <: usize)
  in
  acc

/// @fail(extraction): proverif(HAX0008)
let range2 (n: usize) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (n +! mk_usize 10 <: usize)
      (fun acc temp_1_ ->
          let acc:usize = acc in
          let _:usize = temp_1_ in
          true)
      acc
      (fun acc i ->
          let acc:usize = acc in
          let i:usize = i in
          (acc +! i <: usize) +! mk_usize 1 <: usize)
  in
  acc

/// @fail(extraction): proverif(HAX0008)
let composed_range (n: usize) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Chain.t_Chain
              (Core.Ops.Range.t_Range usize) (Core.Ops.Range.t_Range usize))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Iterator.f_chain #(Core.Ops.Range.t_Range usize)
              #FStar.Tactics.Typeclasses.solve
              #(Core.Ops.Range.t_Range usize)
              ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = n }
                <:
                Core.Ops.Range.t_Range usize)
              ({
                  Core.Ops.Range.f_start = n +! mk_usize 10 <: usize;
                  Core.Ops.Range.f_end = n +! mk_usize 50 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Iter.Adapters.Chain.t_Chain (Core.Ops.Range.t_Range usize)
              (Core.Ops.Range.t_Range usize))
        <:
        Core.Iter.Adapters.Chain.t_Chain (Core.Ops.Range.t_Range usize)
          (Core.Ops.Range.t_Range usize))
      acc
      (fun acc i ->
          let acc:usize = acc in
          let i:usize = i in
          (acc +! i <: usize) +! mk_usize 1 <: usize)
  in
  acc

/// @fail(extraction): proverif(HAX0008)
let rev_range (n: usize) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Rev.t_Rev
            (Core.Ops.Range.t_Range usize))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Iterator.f_rev #(Core.Ops.Range.t_Range usize)
              #FStar.Tactics.Typeclasses.solve
              ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = n }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Iter.Adapters.Rev.t_Rev (Core.Ops.Range.t_Range usize))
        <:
        Core.Iter.Adapters.Rev.t_Rev (Core.Ops.Range.t_Range usize))
      acc
      (fun acc i ->
          let acc:usize = acc in
          let i:usize = i in
          (acc +! i <: usize) +! mk_usize 1 <: usize)
  in
  acc

/// @fail(extraction): proverif(HAX0008, HAX0008)
let chunks (v_CHUNK_LEN: usize) (arr: Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global) : usize =
  let acc:usize = mk_usize 0 in
  let chunks:Core.Slice.Iter.t_ChunksExact usize =
    Core.Slice.impl__chunks_exact #usize
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          arr
        <:
        t_Slice usize)
      v_CHUNK_LEN
  in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_ChunksExact
            usize)
          #FStar.Tactics.Typeclasses.solve
          (Core.Clone.f_clone #(Core.Slice.Iter.t_ChunksExact usize)
              #FStar.Tactics.Typeclasses.solve
              chunks
            <:
            Core.Slice.Iter.t_ChunksExact usize)
        <:
        Core.Slice.Iter.t_ChunksExact usize)
      acc
      (fun acc chunk ->
          let acc:usize = acc in
          let chunk:t_Slice usize = chunk in
          let mean:usize = mk_usize 0 in
          let mean:usize =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice usize)
                  #FStar.Tactics.Typeclasses.solve
                  chunk
                <:
                Core.Slice.Iter.t_Iter usize)
              mean
              (fun mean item ->
                  let mean:usize = mean in
                  let item:usize = item in
                  mean +! item <: usize)
          in
          let acc:usize = acc +! (mean /! v_CHUNK_LEN <: usize) in
          acc)
  in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice usize)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.Iter.impl_88__remainder #usize chunks <: t_Slice usize)
        <:
        Core.Slice.Iter.t_Iter usize)
      acc
      (fun acc item ->
          let acc:usize = acc in
          let item:usize = item in
          acc -! item <: usize)
  in
  acc

/// @fail(extraction): proverif(HAX0008)
let iterator (arr: Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            usize)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #usize
              (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  arr
                <:
                t_Slice usize)
            <:
            Core.Slice.Iter.t_Iter usize)
        <:
        Core.Slice.Iter.t_Iter usize)
      acc
      (fun acc item ->
          let acc:usize = acc in
          let item:usize = item in
          acc +! item <: usize)
  in
  acc

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0008)
let nested (arr: Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            usize)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #usize
              (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  arr
                <:
                t_Slice usize)
            <:
            Core.Slice.Iter.t_Iter usize)
        <:
        Core.Slice.Iter.t_Iter usize)
      acc
      (fun acc item ->
          let acc:usize = acc in
          let item:usize = item in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Rev.t_Rev
                  (Core.Ops.Range.t_Range usize))
                #FStar.Tactics.Typeclasses.solve
                (Core.Iter.Traits.Iterator.f_rev #(Core.Ops.Range.t_Range usize)
                    #FStar.Tactics.Typeclasses.solve
                    ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = item }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Core.Iter.Adapters.Rev.t_Rev (Core.Ops.Range.t_Range usize))
              <:
              Core.Iter.Adapters.Rev.t_Rev (Core.Ops.Range.t_Range usize))
            acc
            (fun acc i ->
                let acc:usize = acc in
                let i:usize = i in
                let acc:usize = acc +! mk_usize 1 in
                Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Zip.t_Zip
                          (Core.Slice.Iter.t_Iter usize) (Core.Ops.Range.t_Range usize))
                      #FStar.Tactics.Typeclasses.solve
                      (Core.Iter.Traits.Iterator.f_zip #(Core.Slice.Iter.t_Iter usize)
                          #FStar.Tactics.Typeclasses.solve
                          #(Core.Ops.Range.t_Range usize)
                          (Core.Slice.impl__iter #usize
                              (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
                                  #FStar.Tactics.Typeclasses.solve
                                  arr
                                <:
                                t_Slice usize)
                            <:
                            Core.Slice.Iter.t_Iter usize)
                          ({ Core.Ops.Range.f_start = mk_usize 4; Core.Ops.Range.f_end = i }
                            <:
                            Core.Ops.Range.t_Range usize)
                        <:
                        Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter usize)
                          (Core.Ops.Range.t_Range usize))
                    <:
                    Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter usize)
                      (Core.Ops.Range.t_Range usize))
                  acc
                  (fun acc j ->
                      let acc:usize = acc in
                      let j:(usize & usize) = j in
                      (((acc +! item <: usize) +! i <: usize) +! j._1 <: usize) +! j._2 <: usize))
          <:
          usize)
  in
  acc

/// @fail(extraction): proverif(HAX0008)
let pattern (arr: Alloc.Vec.t_Vec (usize & usize) Alloc.Alloc.t_Global) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
              (usize & usize) Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          arr
        <:
        Alloc.Vec.Into_iter.t_IntoIter (usize & usize) Alloc.Alloc.t_Global)
      acc
      (fun acc temp_1_ ->
          let acc:usize = acc in
          let x, y:(usize & usize) = temp_1_ in
          acc +! (x *! y <: usize) <: usize)
  in
  acc

/// @fail(extraction): proverif(HAX0008)
let enumerate_chunks (arr: Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global) : usize =
  let acc:usize = mk_usize 0 in
  let acc:usize =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Chunks usize))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Iterator.f_enumerate #(Core.Slice.Iter.t_Chunks usize)
              #FStar.Tactics.Typeclasses.solve
              (Core.Slice.impl__chunks #usize
                  (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec usize Alloc.Alloc.t_Global)
                      #FStar.Tactics.Typeclasses.solve
                      arr
                    <:
                    t_Slice usize)
                  (mk_usize 4)
                <:
                Core.Slice.Iter.t_Chunks usize)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks usize))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks usize))
      acc
      (fun acc temp_1_ ->
          let acc:usize = acc in
          let i, chunk:(usize & t_Slice usize) = temp_1_ in
          Rust_primitives.Hax.Folds.fold_enumerated_slice chunk
            (fun acc temp_1_ ->
                let acc:usize = acc in
                let _:usize = temp_1_ in
                true)
            acc
            (fun acc temp_1_ ->
                let acc:usize = acc in
                let j, x:(usize & usize) = temp_1_ in
                (i +! j <: usize) +! x <: usize)
          <:
          usize)
  in
  acc

let bool_returning (x: u8) : bool = x <. mk_u8 10

/// @fail(extraction): proverif(HAX0008)
let f (_: Prims.unit) : (u8 & Prims.unit) =
  let acc:u8 = mk_u8 0 in
  Rust_primitives.Hax.Folds.fold_range (mk_u8 1)
    (mk_u8 10)
    (fun acc temp_1_ ->
        let acc:u8 = acc in
        let _:u8 = temp_1_ in
        true)
    acc
    (fun acc i ->
        let acc:u8 = acc in
        let i:u8 = i in
        let acc:u8 = acc +! i in
        let _:bool = bool_returning i in
        acc),
  ()
  <:
  (u8 & Prims.unit)
