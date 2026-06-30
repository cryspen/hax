import CoreModels.Alloc.Funs

namespace CoreModels
namespace core

/-!

# Funs Epilogue

This file contains workarounds required to be present **after** `Funs.lean` runs.

See `FunsEpilogue.lean` for workarounds that run before `Funs.lean`.

-/

/-! ## core::iter::range — Range iteration

Aeneas extracts `for i in lo..hi { … }` to a loop driven by
`core.iter.range.IteratorRange.next`, which in turn uses a
`core.iter.range.Step` dictionary. We provide both, plus a `StepUsize`
instance, so that downstream extracted code that iterates over `Range<usize>`
type-checks. -/

namespace iter.range

/-- The `Iterator::next` implementation for `core::ops::range::Range<A>`,
    parameterised over the `Step` dictionary. -/
def IteratorRange.next {A : Type} (StepInst : Step A) :
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

end iter.range

abbrev ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next :=
  @iter.range.IteratorRange.next

end core

namespace alloc

/-! ## `IntoIter::map` (a provided `Iterator` method)

`map` lives on the extraction-excluded `IteratorMethods` trait, so Aeneas
never synthesises the per-impl `Iterator::map` specialisation that a
downstream crate references when it writes `v.into_iter().map(f)`. We supply
it by hand, mirroring Aeneas's own builtin `Aeneas/Std/VecIter.lean` (which
this project shadows via `open Aeneas.Std hiding namespace core alloc`).

The body just builds the
`Map` adapter; iteration then runs through `Map`'s own `Iterator` instance.
`F` is the closure, `T` the item, `O` its output (the `FnMut` instance is
irrelevant to the model, hence `_`-prefixed). -/
def vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.map
  {T O F : Type} (_FnMutInst : core.ops.function.FnMut F T O) :
  vec.into_iter.IntoIter T → F →
  Aeneas.Std.Result (core.iter.adapters.map.Map (vec.into_iter.IntoIter T) F) :=
  fun it f => .ok { iter := it, f := f }

/-! ## `FromIterator<T>` for `VecDeque<T, Global>`

Like `Vec`'s `FromIterator`, this impl is `--exclude`d from charon: alloc
implements *std*'s `FromIterator`, whose `from_iter<I: IntoIterator<Item = A>>`
pins the iterator's `Item` to the element type, which cannot match
core-models' deliberately bound-free `FromIterator::from_iter<T: IntoIterator>`
(its `Clause0_Item` is a free implicit). So we supply the instance by hand,
binding `Item` free to match the trait field.

NOTE: this is a *stub* — `from_iter` returns an empty deque. We cannot model
the real collect: core-models' `IntoIterator` carries no `Iterator`
super-instance (the `iteratorIteratorInst` field was dropped), so there is no
`next` to drive a fold here. Refine if downstream reasoning depends on the
contents of a `VecDeque::from_iter` result. -/
opaque collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter
  (T : Type) : {T_1 Clause0_Item Clause0_IntoIter : Type} →
  core.iter.traits.collect.IntoIterator T_1 Clause0_Item Clause0_IntoIter →
  T_1 → Aeneas.Std.Result (VecDeque T alloc.Global)

def collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator
  (T : Type) :
  core.iter.traits.collect.FromIterator
    (collections.vec_deque.VecDeque T alloc.Global) T := {
  from_iter := collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter T
}

/-! ## `[T]::to_vec` and `Box<[T]>::into_vec`

Aeneas's builtin name map turns `<[T]>::to_vec` into a reference to
`alloc.slice.Slice.to_vec` (and similarly for `into_vec`). Our local
`alloc/` crate provides those bodies, but under the `alloc.slice.Dummy`
namespace because of the standard "you can't `impl` for a foreign slice
type" workaround. Re-export them at the std-map name so downstream
extractions land on a defined symbol.
-/

noncomputable section

@[rust_fun "alloc::slice::{[@T]}::to_vec"]
def slice.Slice.to_vec
  {T : Type} (cloneInst : core.clone.Clone T) (s : Aeneas.Std.Slice T) :
  Aeneas.Std.Result (vec.Vec T) :=
  slice.Dummy.to_vec cloneInst s

@[rust_fun "alloc::slice::{alloc::boxed::Box<[@T], @A>}::into_vec"]
def slice.Slice.into_vec
  {T : Type} (s : Aeneas.Std.Slice T) : Aeneas.Std.Result (vec.Vec T) :=
  slice.Dummy.into_vec s

end

end alloc
end CoreModels
