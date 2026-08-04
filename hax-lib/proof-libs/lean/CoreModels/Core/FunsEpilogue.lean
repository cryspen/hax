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

/-- Downstream `?` references this `Try::branch` impl under the un-suffixed name
    `…CoreOpsTry_traitTry.branch`, but our own extraction suffixes it
    `…TResultInfallibleE.branch`. Alias so `?` on `Result` elaborates. -/
abbrev result.Result.Insts.CoreOpsTry_traitTry.branch :=
  @result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch

/-! ## Provided `Iterator` methods

`map` / `all` / `collect` are *provided* (default) methods of real `core`'s
`Iterator`, so a downstream crate that writes `it.map(f)` references
`core.iter.traits.iterator.Iterator.map.default`, passing the `Self: Iterator`
dictionary followed by the `FnMut` witness. `core_models` parks these methods
on the extraction-excluded `IteratorMethods` trait, so nothing supplies those
names.

Declaring them as default methods on our own `Iterator` does *not* work: their
bodies never call `next`, so Aeneas prunes the unused `Self: Iterator` clause
and emits `map.default` without the leading dictionary that downstream always
passes (it also pins `F: Fn`, where downstream passes `FnMut`). There is no
flag to keep a pruned clause, so we write these by hand at the signature
downstream actually uses.

These are keyed only on the *trait*, not on the implementing type, so a single
definition serves every iterator — unlike the per-impl `…Insts.<Impl>.map`
shims, which would need one copy per iterator type. -/

/-- `<I as Iterator>::map`. The default body just builds the adapter; iteration
    happens through `Map`'s own `Iterator` instance, so neither witness is used
    here. -/
def iter.traits.iterator.Iterator.map.default
  {Self Item O F : Type}
  (_IteratorInst : iter.traits.iterator.Iterator Self Item)
  (_FnMutInst : ops.function.FnMut F Item O)
  (self : Self) (f : F) :
  Aeneas.Std.Result (iter.adapters.map.Map Self F) :=
  .ok { iter := self, f := f }

/-- Short-circuiting `all` over a list: returns the verdict together with how
    many elements were consumed. Structural on the list, so no `loop` is
    needed. The closure state is threaded through `call_mut`, and a failing
    element is consumed before stopping (Rust leaves the iterator positioned
    *after* it). -/
def iterAllCount {T F : Type} (FnMutInst : ops.function.FnMut F T Bool) :
    F → List T → Aeneas.Std.Result (Bool × Nat)
  | _, [] => .ok (true, 0)
  | f, x :: xs => do
    let (b, f') ← FnMutInst.call_mut f x
    if b then
      let (r, n) ← iterAllCount FnMutInst f' xs
      .ok (r, n + 1)
    else .ok (false, 1)

/-- `<slice::Iter<'_, T> as Iterator>::all`. Takes `&mut self`, so Aeneas's
    encoding returns the verdict paired with the advanced iterator. -/
def slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
  {T F : Type}
  (FnMutInst : ops.function.FnMut F T Bool)
  (self : slice.iter.Iter T) (f : F) :
  Aeneas.Std.Result (Bool × slice.iter.Iter T) := do
  let s : Aeneas.Std.Slice T := self
  let (b, n) ← iterAllCount FnMutInst f s.val
  .ok (b, (⟨s.val.drop n, by have := s.property; simp; omega⟩ : Aeneas.Std.Slice T))

/-- The blanket `impl<I: Iterator> IntoIterator for I`: an iterator is its own
    `IntoIter`. `collect` needs it to hand `self` to `from_iter`. -/
def iter.traits.collect.IntoIterator.ofIterator {Self Item : Type} :
    iter.traits.collect.IntoIterator Self Item Self :=
  { into_iter := fun s => .ok s }

/-- `<I as Iterator>::collect`. Both witnesses are forwarded to `from_iter`,
    which is where the actual draining happens — the `Iterator` dictionary is
    exactly the method-level bound added to `FromIterator` for this purpose. -/
def iter.traits.iterator.Iterator.collect.default
  {Self Item B : Type}
  (IteratorInst : iter.traits.iterator.Iterator Self Item)
  (FromIteratorInst : iter.traits.collect.FromIterator B Item)
  (self : Self) : Aeneas.Std.Result B :=
  FromIteratorInst.from_iter iter.traits.collect.IntoIterator.ofIterator
    IteratorInst self

/-- Drain an iterator into a list. A generic `Iterator` exposes no measure, so
    this is Aeneas's `loop` (the same combinator its own extraction of
    `iter_fold` uses) and lives in the divergence monad: an infinite iterator
    yields `div` rather than a bogus finite answer. -/
def iterDrain {I Item : Type} (IteratorInst : iter.traits.iterator.Iterator I Item)
    (it : I) : Aeneas.Std.Result (List Item) := do
  let acc ← Aeneas.Std.loop
    (fun (it, acc) => do
      let (o, it') ← IteratorInst.next it
      match o with
      | option.Option.Some x => .ok (.cont (it', x :: acc))
      | option.Option.None   => .ok (.done acc))
    (it, ([] : List Item))
  .ok acc.reverse

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

/-! ## `FromIterator<T>` for `Vec<T>`

Charon-excluded (see `ALLOC_CHARON_EXCLUDES`): Aeneas fails on the impl's
`for el in iter` body with `Could not find: type_var_id: 1`. Supplied here
instead — and unlike the `VecDeque` stub below this is a *real* body, because
`FromIterator::from_iter` now carries the `Iterator` witness needed to drain
the source. -/

/-- A `Vec` is a length-bounded list, so building one from a drained iterator
    is fallible: an over-long result panics rather than silently truncating. -/
def vec.ofList {T : Type} (l : List T) : Aeneas.Std.Result (vec.Vec T) :=
  if h : l.length ≤ Aeneas.Std.Usize.max then .ok ⟨l, h⟩ else .fail .panic

def vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter (T : Type)
  {U IntoIter : Type}
  (IntoIteratorInst : core.iter.traits.collect.IntoIterator U T IntoIter)
  (IteratorInst : core.iter.traits.iterator.Iterator IntoIter T)
  (u : U) : Aeneas.Std.Result (vec.Vec T) := do
  let it ← IntoIteratorInst.into_iter u
  let l ← core.iterDrain IteratorInst it
  vec.ofList l

def vec.Vec.Insts.CoreIterTraitsCollectFromIterator (T : Type) :
    core.iter.traits.collect.FromIterator (vec.Vec T) T :=
  { from_iter := vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter T }

/-! ## `FromIterator<T>` for `VecDeque<T, Global>`

Like `Vec`'s `FromIterator`, this impl is `--exclude`d from charon, so the
instance is supplied here.

The exclusion originally existed because *std*'s `from_iter<I: IntoIterator<
Item = A>>` pins the iterator's `Item`, which could not match core-models'
then-bound-free `from_iter<T: IntoIterator>`. `Item` is pinned on our side too
now, so that particular mismatch is gone; what keeps both impls excluded is
that Aeneas fails on their `for el in iter` bodies.

This used to be a stub returning an empty deque, because there was no `next`
reachable from `from_iter`'s arguments. The method-level `Iterator` bound on
`FromIterator` supplies one, so it is now a real body — the same drain the
`Vec` instance above uses. -/
def collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter
  (T : Type) {U IntoIter : Type}
  (IntoIteratorInst : core.iter.traits.collect.IntoIterator U T IntoIter)
  (IteratorInst : core.iter.traits.iterator.Iterator IntoIter T)
  (u : U) : Aeneas.Std.Result (VecDeque T alloc.Global) := do
  let it ← IntoIteratorInst.into_iter u
  let l ← core.iterDrain IteratorInst it
  let v ← vec.ofList l
  .ok ((v : Aeneas.Std.Slice T), core.marker.PhantomData.mk)

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
