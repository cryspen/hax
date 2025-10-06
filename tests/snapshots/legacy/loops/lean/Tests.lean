
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Tests.Legacy__loops.For_loops.range1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (15 : usize)
        (fun acc _ => (do true : Result Bool))
        acc
        (fun acc i => (do (← acc +? i) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.range2 (n : usize) : Result usize := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (← n +? (10 : usize))
        (fun acc _ => (do true : Result Bool))
        acc
        (fun acc i => (do (← (← acc +? i) +? (1 : usize)) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.composed_range
  (n : usize)
  : Result usize
  := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
            (← Core.Iter.Traits.Iterator.Iterator.chain
                (Core.Ops.Range.Range usize)
                (Core.Ops.Range.Range.mk (start := (0 : usize)) (_end := n))
                (Core.Ops.Range.Range.mk
                  (start := (← n +? (10 : usize)))
                  (_end := (← n +? (50 : usize))))))
        acc
        (fun acc i => (do (← (← acc +? i) +? (1 : usize)) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.rev_range (n : usize) : Result usize := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
            (← Core.Iter.Traits.Iterator.Iterator.rev
                (Core.Ops.Range.Range.mk (start := (0 : usize)) (_end := n))))
        acc
        (fun acc i => (do (← (← acc +? i) +? (1 : usize)) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.chunks
  -- Unsupported const param (arr : (Alloc.Vec.Vec usize Alloc.Alloc.Global))
  : Result usize
  := do
  let acc : usize ← (pure (0 : usize));
  let chunks : (Core.Slice.Iter.ChunksExact usize) ← (pure
    (← Core.Slice.Impl.chunks_exact usize
        (← Core.Ops.Deref.Deref.deref arr)
        CHUNK_LEN));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
            (← Core.Clone.Clone.clone chunks))
        acc
        (fun acc chunk => (do
            let mean : usize ← (pure (0 : usize));
            let mean : usize ← (pure
              (← Core.Iter.Traits.Iterator.Iterator.fold
                  (← Core.Iter.Traits.Collect.IntoIterator.into_iter chunk)
                  mean
                  (fun mean item => (do (← mean +? item) : Result usize))));
            let acc : usize ← (pure (← acc +? (← mean /? CHUNK_LEN)));
            acc : Result usize))));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
            (← Core.Slice.Iter.Impl_88.remainder usize chunks))
        acc
        (fun acc item => (do (← acc -? item) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.iterator
  (arr : (Alloc.Vec.Vec usize Alloc.Alloc.Global))
  : Result usize
  := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
            (← Core.Slice.Impl.iter usize (← Core.Ops.Deref.Deref.deref arr)))
        acc
        (fun acc item => (do (← acc +? item) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.nested
  (arr : (Alloc.Vec.Vec usize Alloc.Alloc.Global))
  : Result usize
  := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
            (← Core.Slice.Impl.iter usize (← Core.Ops.Deref.Deref.deref arr)))
        acc
        (fun acc item => (do
            (← Core.Iter.Traits.Iterator.Iterator.fold
                (← Core.Iter.Traits.Collect.IntoIterator.into_iter
                    (← Core.Iter.Traits.Iterator.Iterator.rev
                        (Core.Ops.Range.Range.mk
                          (start := (0 : usize)) (_end := item))))
                acc
                (fun acc i => (do
                    let acc : usize ← (pure (← acc +? (1 : usize)));
                    (← Core.Iter.Traits.Iterator.Iterator.fold
                        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
                            (← Core.Iter.Traits.Iterator.Iterator.zip
                                (Core.Ops.Range.Range usize)
                                (← Core.Slice.Impl.iter usize
                                    (← Core.Ops.Deref.Deref.deref arr))
                                (Core.Ops.Range.Range.mk
                                  (start := (4 : usize)) (_end := i))))
                        acc
                        (fun acc j => (do
                            (← (← (← (← acc +? item) +? i)
                                +? (Rust_primitives.Hax.Tuple0._0 j))
                              +? (Rust_primitives.Hax.Tuple0._1 j)) : Result
                            usize))) : Result usize))) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.pattern
  (arr :
  (Alloc.Vec.Vec (Rust_primitives.Hax.Tuple2 usize usize) Alloc.Alloc.Global))
  : Result usize
  := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter arr)
        acc
        (fun acc ⟨x, y⟩ => (do (← acc +? (← x *? y)) : Result usize))));
  acc

def Tests.Legacy__loops.For_loops.enumerate_chunks
  (arr : (Alloc.Vec.Vec usize Alloc.Alloc.Global))
  : Result usize
  := do
  let acc : usize ← (pure (0 : usize));
  let acc : usize ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter
            (← Core.Iter.Traits.Iterator.Iterator.enumerate
                (← Core.Slice.Impl.chunks usize
                    (← Core.Ops.Deref.Deref.deref arr)
                    (4 : usize))))
        acc
        (fun acc ⟨i, chunk⟩ => (do
            (← Rust_primitives.Hax.Folds.fold_enumerated_slice
                chunk
                (fun acc _ => (do true : Result Bool))
                acc
                (fun acc ⟨j, x⟩ => (do (← (← i +? j) +? x) : Result usize))) :
            Result usize))));
  acc

def Tests.Legacy__loops.For_loops.bool_returning (x : u8) : Result Bool := do
  (← Rust_primitives.Hax.Machine_int.lt x (10 : u8))

def Tests.Legacy__loops.For_loops.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 u8 Rust_primitives.Hax.Tuple0)
  := do
  let acc : u8 ← (pure (0 : u8));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.Folds.fold_range
        (1 : u8)
        (10 : u8)
        (fun acc _ => (do true : Result Bool))
        acc
        (fun acc i => (do
            let acc : u8 ← (pure (← acc +? i));
            let _ ← (pure (← Tests.Legacy__loops.For_loops.bool_returning i));
            acc : Result u8)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__loops.Control_flow.double_sum
  (_ : Rust_primitives.Hax.Tuple0)
  : Result i32
  := do
  let sum : i32 ← (pure (0 : i32));
  let sum : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range_cf
        (1 : i32)
        (10 : i32)
        (fun sum _ => (do true : Result Bool))
        sum
        (fun sum i => (do
            (← if (← Rust_primitives.Hax.Machine_int.lt i (0 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Rust_primitives.Hax.Tuple2.mk
                  Rust_primitives.Hax.Tuple0.mk sum))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← sum +? i))) :
            Result
            (Core.Ops.Control_flow.ControlFlow
              (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32)
              i32)))));
  (← sum *? (2 : i32))

def Tests.Legacy__loops.Control_flow.double_sum2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result i32
  := do
  let sum : i32 ← (pure (0 : i32));
  let sum2 : i32 ← (pure (0 : i32));
  let ⟨sum, sum2⟩ ← (pure
    (← Rust_primitives.Hax.Folds.fold_range_cf
        (1 : i32)
        (10 : i32)
        (fun ⟨sum, sum2⟩ _ => (do true : Result Bool))
        (Rust_primitives.Hax.Tuple2.mk sum sum2)
        (fun ⟨sum, sum2⟩ i => (do
            (← if (← Rust_primitives.Hax.Machine_int.lt i (0 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Rust_primitives.Hax.Tuple2.mk
                  Rust_primitives.Hax.Tuple0.mk
                  (Rust_primitives.Hax.Tuple2.mk sum sum2)))
            else do
              let sum : i32 ← (pure (← sum +? i));
              (Core.Ops.Control_flow.ControlFlow.Continue
                (Rust_primitives.Hax.Tuple2.mk sum (← sum2 +? i)))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Rust_primitives.Hax.Tuple2
                Rust_primitives.Hax.Tuple0
                (Rust_primitives.Hax.Tuple2 i32 i32))
              (Rust_primitives.Hax.Tuple2 i32 i32))))));
  (← sum +? sum2)

def Tests.Legacy__loops.Control_flow.double_sum_return
  (v : (RustSlice i32))
  : Result i32
  := do
  let sum : i32 ← (pure (0 : i32));
  (match
    (← Rust_primitives.Hax.Folds.fold_return
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter v)
        sum
        (fun sum i => (do
            (← if (← Rust_primitives.Hax.Machine_int.lt i (0 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break (0 : i32)))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← sum +? i))) :
            Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                i32
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32))
              i32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue sum)
      => do (← sum *? (2 : i32)))

def Tests.Legacy__loops.Control_flow.double_sum2_return
  (v : (RustSlice i32))
  : Result i32
  := do
  let sum : i32 ← (pure (0 : i32));
  let sum2 : i32 ← (pure (0 : i32));
  (match
    (← Rust_primitives.Hax.Folds.fold_return
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter v)
        (Rust_primitives.Hax.Tuple2.mk sum sum2)
        (fun ⟨sum, sum2⟩ i => (do
            (← if (← Rust_primitives.Hax.Machine_int.lt i (0 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break (0 : i32)))
            else do
              let sum : i32 ← (pure (← sum +? i));
              (Core.Ops.Control_flow.ControlFlow.Continue
                (Rust_primitives.Hax.Tuple2.mk sum (← sum2 +? i)))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                i32
                (Rust_primitives.Hax.Tuple2
                  Rust_primitives.Hax.Tuple0
                  (Rust_primitives.Hax.Tuple2 i32 i32)))
              (Rust_primitives.Hax.Tuple2 i32 i32)))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue ⟨sum, sum2⟩)
      => do (← sum +? sum2))

def Tests.Legacy__loops.Control_flow.bigger_power_2 (x : i32) : Result i32 := do
  let pow : i32 ← (pure (1 : i32));
  (← Rust_primitives.Hax.while_loop_cf
      (fun pow => (do
          (← Rust_primitives.Hax.Machine_int.lt pow (1000000 : i32)) : Result
          Bool))
      (fun pow => (do true : Result Bool))
      (fun pow => (do
          (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
          Hax_lib.Int.Int))
      pow
      (fun pow => (do
          let pow : i32 ← (pure (← pow *? (2 : i32)));
          (← if (← Rust_primitives.Hax.Machine_int.lt pow x) then do
            let pow : i32 ← (pure (← pow *? (3 : i32)));
            (← if true then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Rust_primitives.Hax.Tuple2.mk
                  Rust_primitives.Hax.Tuple0.mk pow))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← pow *? (2 : i32))))
          else do
            (Core.Ops.Control_flow.ControlFlow.Continue (← pow *? (2 : i32)))) :
          Result
          (Core.Ops.Control_flow.ControlFlow
            (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32)
            i32))))

structure Tests.Legacy__loops.Control_flow.M where
  m : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

def Tests.Legacy__loops.Control_flow.Impl.decoded_message
  (self : Tests.Legacy__loops.Control_flow.M)
  : Result (Core.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  := do
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (0 : usize)
        (← Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global
            (Tests.Legacy__loops.Control_flow.M.m self))
        (fun _ _ => (do true : Result Bool))
        Rust_primitives.Hax.Tuple0.mk
        (fun _ i => (do
            (← if (← Rust_primitives.Hax.Machine_int.gt i (5 : usize)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break
                  Core.Option.Option.None))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue
                Rust_primitives.Hax.Tuple0.mk)) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
                (Rust_primitives.Hax.Tuple2
                  Rust_primitives.Hax.Tuple0
                  Rust_primitives.Hax.Tuple0))
              Rust_primitives.Hax.Tuple0))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue _)
      => do
        (Core.Option.Option.Some
          (← Core.Clone.Clone.clone
              (Tests.Legacy__loops.Control_flow.M.m self))))

def Tests.Legacy__loops.Control_flow.nested
  (_ : Rust_primitives.Hax.Tuple0)
  : Result i32
  := do
  let sum : i32 ← (pure (0 : i32));
  let sum : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (1 : i32)
        (10 : i32)
        (fun sum _ => (do true : Result Bool))
        sum
        (fun sum i => (do
            let sum : i32 ← (pure
              (← Rust_primitives.Hax.Folds.fold_range_cf
                  (1 : i32)
                  (10 : i32)
                  (fun sum _ => (do true : Result Bool))
                  sum
                  (fun sum j => (do
                      (← if
                      (← Rust_primitives.Hax.Machine_int.lt j (0 : i32)) then do
                        (Core.Ops.Control_flow.ControlFlow.Break
                          (Rust_primitives.Hax.Tuple2.mk
                            Rust_primitives.Hax.Tuple0.mk sum))
                      else do
                        (Core.Ops.Control_flow.ControlFlow.Continue
                          (← sum +? j))) : Result
                      (Core.Ops.Control_flow.ControlFlow
                        (Rust_primitives.Hax.Tuple2
                          Rust_primitives.Hax.Tuple0
                          i32)
                        i32)))));
            (← sum +? i) : Result i32))));
  (← sum *? (2 : i32))

def Tests.Legacy__loops.Control_flow.nested_return
  (_ : Rust_primitives.Hax.Tuple0)
  : Result i32
  := do
  let sum : i32 ← (pure (0 : i32));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (1 : i32)
        (10 : i32)
        (fun sum _ => (do true : Result Bool))
        sum
        (fun sum i => (do
            (match
              (← Rust_primitives.Hax.Folds.fold_range_return
                  (1 : i32)
                  (10 : i32)
                  (fun sum _ => (do true : Result Bool))
                  sum
                  (fun sum j => (do
                      (← if
                      (← Rust_primitives.Hax.Machine_int.lt j (0 : i32)) then do
                        (Core.Ops.Control_flow.ControlFlow.Break
                          (Core.Ops.Control_flow.ControlFlow.Break (0 : i32)))
                      else do
                        (Core.Ops.Control_flow.ControlFlow.Continue
                          (← sum +? j))) : Result
                      (Core.Ops.Control_flow.ControlFlow
                        (Core.Ops.Control_flow.ControlFlow
                          i32
                          (Rust_primitives.Hax.Tuple2
                            Rust_primitives.Hax.Tuple0
                            i32))
                        i32))))
            with
              | (Core.Ops.Control_flow.ControlFlow.Break ret)
                => do
                  (Core.Ops.Control_flow.ControlFlow.Break
                    (Core.Ops.Control_flow.ControlFlow.Break ret))
              | (Core.Ops.Control_flow.ControlFlow.Continue sum)
                => do (Core.Ops.Control_flow.ControlFlow.Continue (← sum +? i)))
            : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                i32
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32))
              i32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue sum)
      => do (← sum *? (2 : i32)))

def Tests.Legacy__loops.Control_flow.continue_only
  (x : (RustSlice i32))
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
  := do
  let product : i32 ← (pure (1 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Core.Iter.Traits.Iterator.Iterator.fold
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter x)
        product
        (fun product i => (do
            (← if (← Rust_primitives.Hax.Machine_int.eq i (0 : i32)) then do
              product
            else do
              (← Core.Ops.Arith.MulAssign.mul_assign product i)) : Result i32)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__loops.Control_flow.continue_and_break
  (x : (RustSlice i32))
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
  := do
  let product : i32 ← (pure (1 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.Folds.fold_cf
        (← Core.Iter.Traits.Collect.IntoIterator.into_iter x)
        product
        (fun product i => (do
            (← if (← Rust_primitives.Hax.Machine_int.eq i (0 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Continue product)
            else do
              (← if (← Rust_primitives.Hax.Machine_int.lt i (0 : i32)) then do
                (Core.Ops.Control_flow.ControlFlow.Break
                  (Rust_primitives.Hax.Tuple2.mk
                    Rust_primitives.Hax.Tuple0.mk product))
              else do
                (Core.Ops.Control_flow.ControlFlow.Continue
                  (← Core.Ops.Arith.MulAssign.mul_assign product i)))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32)
              i32))))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__loops.While_loops.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u8
  := do
  let x : u8 ← (pure (0 : u8));
  let x : u8 ← (pure
    (← Rust_primitives.Hax.while_loop
        (fun x => (do
            (← Rust_primitives.Hax.Machine_int.lt x (10 : u8)) : Result Bool))
        (fun x => (do true : Result Bool))
        (fun x => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        x
        (fun x => (do let x : u8 ← (pure (← x +? (3 : u8))); x : Result u8))));
  (← x +? (12 : u8))

def Tests.Legacy__loops.While_loops.while_invariant_decr
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u8
  := do
  let x : u8 ← (pure (0 : u8));
  let x : u8 ← (pure
    (← Rust_primitives.Hax.while_loop
        (fun x => (do
            (← Rust_primitives.Hax.Machine_int.lt x (10 : u8)) : Result Bool))
        (fun x => (do
            (← Hax_lib.Prop.Constructors.from_bool
                (← Rust_primitives.Hax.Machine_int.le x (10 : u8))) : Result
            Hax_lib.Prop.Prop))
        (fun x => (do
            (← Rust_primitives.Hax.Int.from_machine (← (10 : u8) -? x)) : Result
            Hax_lib.Int.Int))
        x
        (fun x => (do let x : u8 ← (pure (← x +? (3 : u8))); x : Result u8))));
  (← x +? (12 : u8))

def Tests.Legacy__loops.While_loops.while_invariant_decr_rev
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u8
  := do
  let x : u8 ← (pure (0 : u8));
  let x : u8 ← (pure
    (← Rust_primitives.Hax.while_loop
        (fun x => (do
            (← Rust_primitives.Hax.Machine_int.lt x (10 : u8)) : Result Bool))
        (fun x => (do
            (← Hax_lib.Prop.Constructors.from_bool
                (← Rust_primitives.Hax.Machine_int.le x (10 : u8))) : Result
            Hax_lib.Prop.Prop))
        (fun x => (do
            (← Rust_primitives.Hax.Int.from_machine (← (10 : u8) -? x)) : Result
            Hax_lib.Int.Int))
        x
        (fun x => (do let x : u8 ← (pure (← x +? (3 : u8))); x : Result u8))));
  (← x +? (12 : u8))

def Tests.Legacy__loops.Recognized_loops.range
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 u64 Rust_primitives.Hax.Tuple0)
  := do
  let count : u64 ← (pure (0 : u64));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : u8)
        (10 : u8)
        (fun count i => (do
            (← Rust_primitives.Hax.Machine_int.le i (10 : u8)) : Result Bool))
        count
        (fun count i => (do
            let count : u64 ← (pure (← count +? (1 : u64)));
            count : Result u64)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__loops.Recognized_loops.range_step_by
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 u64 Rust_primitives.Hax.Tuple0)
  := do
  let count : u64 ← (pure (0 : u64));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.Folds.fold_range_step_by
        (0 : u8)
        (10 : u8)
        (2 : usize)
        (fun count i => (do
            (← Rust_primitives.Hax.Machine_int.le i (10 : u8)) : Result Bool))
        count
        (fun count i => (do
            let count : u64 ← (pure (← count +? (1 : u64)));
            count : Result u64)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__loops.Recognized_loops.enumerated_slice
  (T : Type) (slice : (RustSlice T))
  : Result (Rust_primitives.Hax.Tuple2 u64 Rust_primitives.Hax.Tuple0)
  := do
  let count : u64 ← (pure (0 : u64));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.Folds.fold_enumerated_slice
        slice
        (fun count i => (do
            (← Rust_primitives.Hax.Machine_int.le i (10 : usize)) : Result
            Bool))
        count
        (fun count i => (do
            let count : u64 ← (pure (← count +? (2 : u64)));
            count : Result u64)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__loops.Recognized_loops.enumerated_chunked_slice
  (T : Type) (slice : (RustSlice T))
  : Result (Rust_primitives.Hax.Tuple2 u64 Rust_primitives.Hax.Tuple0)
  := do
  let count : u64 ← (pure (0 : u64));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice
        (3 : usize)
        slice
        (fun count i => (do
            (← Hax_lib.Prop.Impl.from_bool true) : Result Hax_lib.Prop.Prop))
        count
        (fun count i => (do
            let count : u64 ← (pure (← count +? (3 : u64)));
            count : Result u64)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__loops.And_mut_side_effect_loop.looping
  (array : (RustArray u8 (5 : usize)))
  : Result (RustArray u8 (5 : usize))
  := do
  let array : (RustArray u8 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (← Core.Slice.Impl.len u8 (← Rust_primitives.unsize array))
        (fun array _ => (do true : Result Bool))
        array
        (fun array i => (do
            (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                array
                i
                (← Rust_primitives.Hax.cast_op i)) : Result
            (RustArray u8 (5 : usize))))));
  array

def Tests.Legacy__loops.And_mut_side_effect_loop.looping_2
  (array : (RustArray u8 (5 : usize)))
  : Result (RustArray u8 (5 : usize))
  := do
  let ⟨array, result⟩ ← (pure
    (Rust_primitives.Hax.Tuple2.mk
      (← Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (← Core.Slice.Impl.len u8 (← Rust_primitives.unsize array))
          (fun array _ => (do true : Result Bool))
          array
          (fun array i => (do
              (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  array
                  i
                  (← Rust_primitives.Hax.cast_op i)) : Result
              (RustArray u8 (5 : usize)))))
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure result);
  array