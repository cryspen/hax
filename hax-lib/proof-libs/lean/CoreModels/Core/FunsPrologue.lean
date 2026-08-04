import CoreModels.Core.Types
import CoreModels.Alloc.Types
import CoreModels.RustPrimitives.Funs

/-!

# Funs Prologue

This file contains workarounds required to be present **before** `Funs.lean` runs. The file
`Funs.lean` contains the functions automatically generated from our Rust implementation of core.
Since it's automatically generated, we cannot move this material there.

-/

namespace CoreModels.core

open Aeneas.Std Result

/-- The `Iterator::next` implementation for `core::ops::range::Range<A>`,
    parameterised over the `Step` dictionary. -/
def IteratorRange.next {A : Type} (StepInst : iter.range.Step A) :
    ops.range.Range A → Aeneas.Std.Result ((Option A) × ops.range.Range A) := fun range => do
  let cmp ← StepInst.corecmpPartialOrdInst.partial_cmp range.start range.«end»
  let isLess : Bool := match cmp with
    | Option.some o => match o with
                       | core.cmp.Ordering.Less => true
                       | _ => false
    | _ => false
  if isLess then
    let cur ← StepInst.cloneCloneInst.clone range.start
    let next? ← StepInst.forward_checked cur 1#usize
    match next? with
    | Option.none      => .fail .panic
    | Option.some next => .ok (Option.some cur, { range with start := next })
  else .ok (Option.none, range)

abbrev ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next :=
  @IteratorRange.next

/-- [core::cmp::impls::{core::cmp::PartialOrd<&0 (B)> for &1 (A)}::lt]:
    Source: '/rustc/library/core/src/cmp.rs', lines 2133:8-2133:40
    Name pattern: [core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::lt]
    Visibility: public -/
@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::lt"]
def Shared1A.Insts.CoreCmpPartialOrdShared0B.lt
  {A : Type} {B : Type} (PartialOrdInst : cmp.PartialOrd A B) :
  A → B → Result Bool := fun a b => do
  let o ← PartialOrdInst.partial_cmp a b
  match o with
  | some cmp.Ordering.Less => ok true
  | _ => ok false

/-- [core::cmp::impls::{core::cmp::PartialOrd<&0 (B)> for &1 (A)}::gt]:
    Source: '/rustc/library/core/src/cmp.rs', lines 2141:8-2141:40
    Name pattern: [core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::gt]
    Visibility: public -/
@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::gt"]
def Shared1A.Insts.CoreCmpPartialOrdShared0B.gt
  {A : Type} {B : Type} (PartialOrdInst : cmp.PartialOrd A B) :
  A → B → Result Bool := fun a b => do
  let o ← PartialOrdInst.partial_cmp a b
  match o with
  | some cmp.Ordering.Greater => ok true
  | _ => ok false


/-! ## Option -/

def option.Option.unwrap_or :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.unwrap_or T x y)

def option.Option.is_some :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_some T x)

def option.Option.is_none :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_none T x)

def option.Option.take :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.take T x)

/-! ## Mem -/

def mem.swap :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.swap T x y)

def mem.replace :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.replace T x y)

/-! ## Redirects to Aeneas's library -/

export Aeneas.Std.core (
  num.U8.MIN num.U8.MAX num.I8.MIN num.I8.MAX
  num.U16.MIN num.U16.MAX num.I16.MIN num.I16.MAX
  num.U32.MIN num.U32.MAX num.I32.MIN num.I32.MAX
  num.U64.MIN num.U64.MAX num.I64.MIN num.I64.MAX
  num.U128.MIN num.U128.MAX num.I128.MIN num.I128.MAX
  num.Usize.MIN num.Usize.MAX num.Isize.MIN num.Isize.MAX
  convert.num.FromU16U8.from
  convert.num.FromU32U8.from
  convert.num.FromU32U16.from
  convert.num.FromU64U8.from
  convert.num.FromU64U16.from
  convert.num.FromU64U32.from
  convert.num.FromU128U8.from
  convert.num.FromU128U16.from
  convert.num.FromU128U32.from
  convert.num.FromU128U64.from
  convert.num.FromUsizeU8.from
  convert.num.FromUsizeU16.from
  convert.num.FromI16I8.from
  convert.num.FromI32I8.from
  convert.num.FromI32I16.from
  convert.num.FromI64I8.from
  convert.num.FromI64I16.from
  convert.num.FromI64I32.from
  convert.num.FromI128I8.from
  convert.num.FromI128I16.from
  convert.num.FromI128I32.from
  convert.num.FromI128I64.from
  convert.num.FromIsizeI8.from
  convert.num.FromIsizeI16.from
)

end CoreModels.core
