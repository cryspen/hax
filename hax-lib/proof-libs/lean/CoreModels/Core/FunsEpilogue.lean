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

/-- Same aliasing as `Result` above, for `?` on `Option`. -/
abbrev option.Option.Insts.CoreOpsTry_traitTry.branch :=
  @option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch

/-! ## `Iterator::collect` (a provided method kept OFF the `Iterator` structure)

`collect` is EAGER, so a `collect` field would be `collect.default SELF`, whose
resolution recurses through `IntoIterator.Blanket SELF` → the IntoIter↔Iterator
coinductivity that makes `impl_def` report `could not resolve recursive fields:
[collect]`. Aeneas.Std handles this by keeping `collect` off the structure and
supplying `collect.default` as a *standalone* function (there `IteratorInst` is
an ordinary parameter, never `SELF`). We mirror that exactly. The body is the
same as Aeneas.Std's: fold `self` through the passed `FromIterator` instance,
wrapping `self` as an `IntoIterator` via the `Blanket` (which now carries the
`iteratorIteratorInst` super-instance, so `from_iter` has `next` to fold with). -/
open Aeneas.Std (Result) in
def iter.traits.iterator.Iterator.collect.default {Self B Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (collectFromIteratorInst : iter.traits.collect.FromIterator B Clause0_Item)
    (self : Self) : Result B :=
  collectFromIteratorInst.from_iter
    (iter.traits.collect.IntoIterator.Blanket IteratorInst) self

/-! ## `Iterator::rev` (a provided method kept OFF the `Iterator` structure)

`rev` cannot be promoted onto the `Iterator` trait like `map`/`enumerate`: its
`Self: DoubleEndedIterator` bound makes the `Iterator` structure reference
`DoubleEndedIterator`, which references `Iterator` back (its supertrait) — a
mutual trait recursion aeneas rejects ("their model will not type-check"). This
is the circularity Aeneas.Std's `Iter.lean` flags, and we resolve it the same
way: keep `rev` off the structure and supply `rev.default`/`rev.trait_default`
as standalone functions here (there the `Iterator`/`DoubleEndedIterator`
instances are ordinary parameters, never `SELF`). The `DoubleEndedIterator`/
`ExactSizeIterator` traits, the `Rev` adapter and its `Iterator::next`
(delegating to `next_back`), and the `next_back` instances for `Range`/slice
`Iter`/`Enumerate` are all generated from the Rust source; only these two
dispatch shims are hand-written. The `@[rust_fun …]` tag maps a downstream
`.rev()` call onto `rev.trait_default` (as in Aeneas.Std). -/
open Aeneas.Std (Result) in
def iter.traits.iterator.Iterator.rev.default {Self : Type}
    (self : Self) : Result (iter.adapters.rev.Rev Self) :=
  iter.adapters.rev.Rev.new self

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::rev"]
def iter.traits.iterator.Iterator.rev.trait_default
    {Self Clause0_Item Clause1_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_DEInst : iter.traits.double_ended.DoubleEndedIterator Self Clause1_Item)
    (self : Self) : Result (iter.adapters.rev.Rev Self) :=
  iter.traits.iterator.Iterator.rev.default self

/-! ## P2c lazy adapters kept OFF the `Iterator` structure — zip / chain / flat_map / flatten

Unlike step_by/take/skip/filter, these cannot be trait fields: their `.default`
takes the SELF `Iterator` instance (the extra `Iterator`/`Fn` bound threads it
in), so a per-instance field `<m> := <m>.default SELF …` self-references the
instance → the same `impl_def: could not resolve recursive fields` wall that
`collect` hits. Supplied here as standalone functions (the instances are
ordinary parameters, never `SELF`), delegating to the generated adapter `.new`
constructors. `@[rust_fun …]` maps a downstream `.<m>()` onto the shim. -/
open Aeneas.Std (Result) in
def iter.traits.iterator.Iterator.zip.default
    {Self I2 Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator I2 Clause1_Item)
    (self : Self) (it2 : I2) : Result (iter.adapters.zip.Zip Self I2) :=
  iter.adapters.zip.Zip.new IteratorInst IteratorInst1 self it2

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::zip"]
def iter.traits.iterator.Iterator.zip.trait_default
    {Self I2 Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator I2 Clause1_Item)
    (self : Self) (it2 : I2) : Result (iter.adapters.zip.Zip Self I2) :=
  iter.traits.iterator.Iterator.zip.default IteratorInst IteratorInst1 self it2

open Aeneas.Std (Result) in
def iter.traits.iterator.Iterator.chain.default
    {Self U Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator U Clause0_Item)
    (self : Self) (other : U) : Result (iter.adapters.chain.Chain Self U) :=
  iter.adapters.chain.Chain.new IteratorInst IteratorInst1 self other

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::chain"]
def iter.traits.iterator.Iterator.chain.trait_default
    {Self U Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator U Clause0_Item)
    (self : Self) (other : U) : Result (iter.adapters.chain.Chain Self U) :=
  iter.traits.iterator.Iterator.chain.default IteratorInst IteratorInst1 self other

open Aeneas.Std (Result) in
def iter.traits.iterator.Iterator.flat_map.default
    {Self U F Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator U Clause1_Item)
    (FnInst : core.ops.function.Fn F Clause0_Item U)
    (self : Self) (f : F) :
    Result (iter.adapters.flat_map.FlatMap Self U F) :=
  iter.adapters.flat_map.FlatMap.new IteratorInst IteratorInst1 FnInst self f

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flat_map"]
def iter.traits.iterator.Iterator.flat_map.trait_default
    {Self U F Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator U Clause1_Item)
    (FnInst : core.ops.function.Fn F Clause0_Item U)
    (self : Self) (f : F) :
    Result (iter.adapters.flat_map.FlatMap Self U F) :=
  iter.traits.iterator.Iterator.flat_map.default
    IteratorInst IteratorInst1 FnInst self f

open Aeneas.Std (Result) in
def iter.traits.iterator.Iterator.flatten.default
    {Self Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator Clause0_Item Clause1_Item)
    (self : Self) :
    Result (iter.adapters.flatten.Flatten Self Clause0_Item Clause1_Item) :=
  iter.adapters.flatten.Flatten.new IteratorInst IteratorInst1 self

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flatten"]
def iter.traits.iterator.Iterator.flatten.trait_default
    {Self Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator Clause0_Item Clause1_Item)
    (self : Self) :
    Result (iter.adapters.flatten.Flatten Self Clause0_Item Clause1_Item) :=
  iter.traits.iterator.Iterator.flatten.default IteratorInst IteratorInst1 self

/-! ## P3 eager consumers kept OFF the `Iterator` structure

These consume the iterator (never build an adapter), so — like `collect` — a
trait field would be `<m> := <m>.default SELF …`, self-referencing the instance
→ the `impl_def` recursive-field wall. Supplied as standalone `@[rust_fun]`-
tagged dispatch functions delegating to the generated opaque `iter_*` loop
helpers (the instances/`Fn`/`Ord` dictionaries are ordinary params, never
`SELF`). `nth` is omitted: its helper `iter_nth` is `aeneas::exclude`d (a Lean
forward-reference to `core.Usize.Insts.CoreIterRangeStep`), so there is no
`iter_nth` to delegate to. `sum`/`product` need `Sum`/`Product` accumulator
traits (declared without instances) and are likewise left for later. -/
open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fold"]
def iter.traits.iterator.Iterator.fold.trait_default
    {Self B F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn F (B × Clause0_Item) B)
    (self : Self) (init : B) (f : F) : Result B :=
  iter.traits.iterator.iter_fold IteratorInst FnInst self init f

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::all"]
def iter.traits.iterator.Iterator.all.trait_default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn F Clause0_Item Bool)
    (self : Self) (f : F) : Result Bool :=
  iter.traits.iterator.iter_all IteratorInst FnInst self f

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def iter.traits.iterator.Iterator.any.trait_default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn F Clause0_Item Bool)
    (self : Self) (f : F) : Result Bool :=
  iter.traits.iterator.iter_any IteratorInst FnInst self f

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find"]
def iter.traits.iterator.Iterator.find.trait_default
    {Self P Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn P Clause0_Item Bool)
    (self : Self) (predicate : P) : Result (option.Option Clause0_Item) := do
  -- `iter_find` threads the `&mut self` (returns the advanced iterator); `find`
  -- consumes `self`, so the returned iterator is discarded.
  let (o, _) ← iter.traits.iterator.iter_find IteratorInst FnInst self predicate
  .ok o

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find_map"]
def iter.traits.iterator.Iterator.find_map.trait_default
    {Self B F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn F Clause0_Item (option.Option B))
    (self : Self) (f : F) : Result (option.Option B) :=
  iter.traits.iterator.iter_find_map IteratorInst FnInst self f

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::position"]
def iter.traits.iterator.Iterator.position.trait_default
    {Self P Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn P Clause0_Item Bool)
    (self : Self) (predicate : P) : Result (option.Option Aeneas.Std.Usize) :=
  iter.traits.iterator.iter_position IteratorInst FnInst self predicate

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::count"]
def iter.traits.iterator.Iterator.count.trait_default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) : Result Aeneas.Std.Usize :=
  iter.traits.iterator.iter_count IteratorInst self

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::last"]
def iter.traits.iterator.Iterator.last.trait_default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) : Result (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_last IteratorInst self

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::for_each"]
def iter.traits.iterator.Iterator.for_each.trait_default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn F Clause0_Item Unit)
    (self : Self) (f : F) : Result Unit :=
  iter.traits.iterator.iter_for_each IteratorInst FnInst self f

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::reduce"]
def iter.traits.iterator.Iterator.reduce.trait_default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.Fn F (Clause0_Item × Clause0_Item) Clause0_Item)
    (self : Self) (f : F) : Result (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_reduce IteratorInst FnInst self f

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::min"]
def iter.traits.iterator.Iterator.min.trait_default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (OrdInst : cmp.Ord Clause0_Item)
    (self : Self) : Result (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_min IteratorInst OrdInst self

open Aeneas.Std (Result) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::max"]
def iter.traits.iterator.Iterator.max.trait_default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (OrdInst : cmp.Ord Clause0_Item)
    (self : Self) : Result (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_max IteratorInst OrdInst self

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

/-! ## Real (computable) `FromIterator<T>` for `Vec<T>`

`collect::<Vec<_>>()` is idiomatic and must be executable. The Rust impl folds
via `next` into a `Vec` (`vec.Vec.push`), but Aeneas can't extract it — it hits
`type_var_id` resolving the `IntoIterator::Item` associated type (the same aeneas
bug the carve saw), so the impl stays `--exclude`d and we hand-write it, exactly
as Aeneas.Std hand-writes `alloc.vec.FromIteratorVec`. This is a genuine fold, not
the empty stub the VecDeque one is — `IntoIterator` now carries `iteratorIteratorInst`
(the `IntoIter: Iterator` bound), and `FromIterator::from_iter` pins `Item = A`, so
the fold type-checks and `collect` is computable. -/
open Aeneas.Std (Result) in
def vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop
    {T IntoIter : Type}
    (iterInst : core.iter.traits.iterator.Iterator IntoIter T)
    (it : IntoIter) (res : vec.Vec T) : Result (vec.Vec T) := do
  let (o, it1) ← iterInst.next it
  match o with
  | core.option.Option.None => .ok res
  | core.option.Option.Some x =>
    let res1 ← vec.Vec.push res x
    vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop iterInst it1 res1
partial_fixpoint

open Aeneas.Std (Result) in
def vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter
    {T I IntoIter : Type}
    (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter)
    (iter : I) : Result (vec.Vec T) := do
  let res ← vec.Vec.new T
  let it ← IntoIteratorInst.into_iter iter
  vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop
    IntoIteratorInst.iteratorIteratorInst it res

@[reducible]
def vec.Vec.Insts.CoreIterTraitsCollectFromIterator (T : Type) :
    core.iter.traits.collect.FromIterator (vec.Vec T) T := {
  from_iter := fun {T1 Clause0_IntoIter : Type}
    (IntoIteratorInst : core.iter.traits.collect.IntoIterator T1 T Clause0_IntoIter) =>
    vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter IntoIteratorInst
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
