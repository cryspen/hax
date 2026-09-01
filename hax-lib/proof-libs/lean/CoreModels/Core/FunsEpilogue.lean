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

/-- The `Iterator::next` implementation for `core::ops::range::Range<A>`.
    Downstream extractions reference it under this name; the definition itself is
    in `FunsPrologue.lean`, which `Funs.lean` already needs before it. -/
abbrev IteratorRange.next := @_root_.CoreModels.core.IteratorRange.next

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

/-! ## Scalar Debug instances

`Result::{unwrap, expect}` carry std's `E: Debug` bound, so extracted call sites
pass a per-type dictionary. The model only has the blanket `impl<T> Debug for T`
(a concrete `impl Debug for u8` would overlap it), so name the instances here. -/

abbrev U8.Insts.CoreFmtDebug    : fmt.Debug Aeneas.Std.U8    := fmt.Debug.Blanket _
abbrev U16.Insts.CoreFmtDebug   : fmt.Debug Aeneas.Std.U16   := fmt.Debug.Blanket _
abbrev U32.Insts.CoreFmtDebug   : fmt.Debug Aeneas.Std.U32   := fmt.Debug.Blanket _
abbrev U64.Insts.CoreFmtDebug   : fmt.Debug Aeneas.Std.U64   := fmt.Debug.Blanket _
abbrev U128.Insts.CoreFmtDebug  : fmt.Debug Aeneas.Std.U128  := fmt.Debug.Blanket _
abbrev Usize.Insts.CoreFmtDebug : fmt.Debug Aeneas.Std.Usize := fmt.Debug.Blanket _
abbrev I8.Insts.CoreFmtDebug    : fmt.Debug Aeneas.Std.I8    := fmt.Debug.Blanket _
abbrev I16.Insts.CoreFmtDebug   : fmt.Debug Aeneas.Std.I16   := fmt.Debug.Blanket _
abbrev I32.Insts.CoreFmtDebug   : fmt.Debug Aeneas.Std.I32   := fmt.Debug.Blanket _
abbrev I64.Insts.CoreFmtDebug   : fmt.Debug Aeneas.Std.I64   := fmt.Debug.Blanket _
abbrev I128.Insts.CoreFmtDebug  : fmt.Debug Aeneas.Std.I128  := fmt.Debug.Blanket _
abbrev Isize.Insts.CoreFmtDebug : fmt.Debug Aeneas.Std.Isize := fmt.Debug.Blanket _

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
open Aeneas.Std (RustM) in
def iter.traits.iterator.Iterator.collect.default {Self B Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (collectFromIteratorInst : iter.traits.collect.FromIterator B Clause0_Item)
    (self : Self) : RustM B :=
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
-- aeneas emits `Iterator.rev.default (IteratorInst) (DEInst) (self)` at a downstream
-- `.rev()` call (see `iter_rev_range` in `tests/client_test/src/lib.rs`), so THAT
-- is the
-- signature `.default` must have (the dictionaries are ordinary, unused params).
open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::rev"]
def iter.traits.iterator.Iterator.rev.default
    {Self Clause0_Item Clause1_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_DEInst : iter.traits.double_ended.DoubleEndedIterator Self Clause1_Item)
    (self : Self) : RustM (iter.adapters.rev.Rev Self) :=
  iter.adapters.rev.Rev.new self

/-! ## P2c lazy adapters kept OFF the `Iterator` structure — zip / chain / flat_map / flatten

Unlike step_by/take/skip/filter, these cannot be trait fields: their `.default`
takes the SELF `Iterator` instance (the extra `Iterator`/`Fn` bound threads it
in), so a per-instance field `<m> := <m>.default SELF …` self-references the
instance → the same `impl_def: could not resolve recursive fields` wall that
`collect` hits. Supplied here as standalone functions (the instances are
ordinary parameters, never `SELF`), delegating to the generated adapter `.new`
constructors. `@[rust_fun …]` maps a downstream `.<m>()` onto the shim. -/
open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::zip"]
def iter.traits.iterator.Iterator.zip.default
    {Self U Clause0_Item Clause1_Item IntoIter : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IntoIterInst : iter.traits.collect.IntoIterator U Clause1_Item IntoIter)
    (self : Self) (other : U) :
    RustM (iter.adapters.zip.Zip Self IntoIter) := do
  -- std bounds `zip`'s argument by `IntoIterator`, not `Iterator`, so aeneas
  -- passes an `IntoIterator` dictionary here and the result is indexed by
  -- `U::IntoIter`. Take the faithful bound and call `into_iter` (as Aeneas.Std
  -- does); the `Iterator` instance the `Zip` needs comes from the dictionary's
  -- `iteratorIteratorInst` super-field. NOTE: the Rust-side `IteratorMethods`
  -- declaration still says `I2: Iterator` — that trait only feeds the F* lane
  -- and the differential tests, whereas this shim has to match what aeneas
  -- emits from *std*'s signature.
  let b ← IntoIterInst.into_iter other
  iter.adapters.zip.Zip.new IteratorInst IntoIterInst.iteratorIteratorInst self b

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::chain"]
def iter.traits.iterator.Iterator.chain.default
    {Self U Clause0_Item IntoIter : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IntoIterInst : iter.traits.collect.IntoIterator U Clause0_Item IntoIter)
    (self : Self) (other : U) :
    RustM (iter.adapters.chain.Chain Self IntoIter) := do
  -- As `zip` above: std's bound is `U: IntoIterator<Item = Self::Item>`.
  let b ← IntoIterInst.into_iter other
  iter.adapters.chain.Chain.new IteratorInst IntoIterInst.iteratorIteratorInst self b

open Aeneas.Std (RustM) in
def iter.traits.iterator.Iterator.flat_map.default
    {Self U F Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator U Clause1_Item)
    (FnInst : core.ops.function.FnMut F Clause0_Item U)
    (self : Self) (f : F) :
    RustM (iter.adapters.flat_map.FlatMap Self U F) :=
  iter.adapters.flat_map.FlatMap.new IteratorInst IteratorInst1 FnInst self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flat_map"]
def iter.traits.iterator.Iterator.flat_map.trait_default
    {Self U F Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator U Clause1_Item)
    (FnInst : core.ops.function.FnMut F Clause0_Item U)
    (self : Self) (f : F) :
    RustM (iter.adapters.flat_map.FlatMap Self U F) :=
  iter.traits.iterator.Iterator.flat_map.default
    IteratorInst IteratorInst1 FnInst self f

open Aeneas.Std (RustM) in
def iter.traits.iterator.Iterator.flatten.default
    {Self Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator Clause0_Item Clause1_Item)
    (self : Self) :
    RustM (iter.adapters.flatten.Flatten Self Clause0_Item Clause1_Item) :=
  iter.adapters.flatten.Flatten.new IteratorInst IteratorInst1 self

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flatten"]
def iter.traits.iterator.Iterator.flatten.trait_default
    {Self Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator Clause0_Item Clause1_Item)
    (self : Self) :
    RustM (iter.adapters.flatten.Flatten Self Clause0_Item Clause1_Item) :=
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
open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fold"]
def iter.traits.iterator.Iterator.fold.default
    {Self B F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut F (B × Clause0_Item) B)
    (self : Self) (init : B) (f : F) : RustM B :=
  iter.traits.iterator.iter_fold IteratorInst FnInst self init f

open Aeneas.Std (RustM) in
-- `all`/`any`/`find`/`find_map`/`position` take `&mut self` in std, so aeneas's
-- `&mut` translation makes the call site destructure a `(result, iterator)` pair.
-- The shims return that pair rather than a bare result, threading the advanced
-- iterator straight out of the `iter_*` helper (which now takes `&mut I`).
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::all"]
def iter.traits.iterator.Iterator.all.default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut F Clause0_Item Bool)
    (self : Self) (f : F) : RustM (Bool × Self) :=
  iter.traits.iterator.iter_all IteratorInst FnInst self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def iter.traits.iterator.Iterator.any.default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut F Clause0_Item Bool)
    (self : Self) (f : F) : RustM (Bool × Self) :=
  iter.traits.iterator.iter_any IteratorInst FnInst self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find"]
def iter.traits.iterator.Iterator.find.default
    {Self P Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut P Clause0_Item Bool)
    (self : Self) (predicate : P) :
    RustM ((option.Option Clause0_Item) × Self) :=
  iter.traits.iterator.iter_find IteratorInst FnInst self predicate

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find_map"]
def iter.traits.iterator.Iterator.find_map.default
    {Self B F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut F Clause0_Item (option.Option B))
    (self : Self) (f : F) : RustM ((option.Option B) × Self) :=
  iter.traits.iterator.iter_find_map IteratorInst FnInst self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::position"]
def iter.traits.iterator.Iterator.position.default
    {Self P Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut P Clause0_Item Bool)
    (self : Self) (predicate : P) :
    RustM ((option.Option Aeneas.Std.Usize) × Self) :=
  iter.traits.iterator.iter_position IteratorInst FnInst self predicate

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::count"]
def iter.traits.iterator.Iterator.count.default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) : RustM Aeneas.Std.Usize :=
  iter.traits.iterator.iter_count IteratorInst self

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::last"]
def iter.traits.iterator.Iterator.last.default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) : RustM (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_last IteratorInst self

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::for_each"]
def iter.traits.iterator.Iterator.for_each.default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut F Clause0_Item Unit)
    (self : Self) (f : F) : RustM Unit :=
  iter.traits.iterator.iter_for_each IteratorInst FnInst self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::reduce"]
def iter.traits.iterator.Iterator.reduce.default
    {Self F Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (FnInst : core.ops.function.FnMut F (Clause0_Item × Clause0_Item) Clause0_Item)
    (self : Self) (f : F) : RustM (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_reduce IteratorInst FnInst self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::min"]
def iter.traits.iterator.Iterator.min.default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (OrdInst : cmp.Ord Clause0_Item)
    (self : Self) : RustM (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_min IteratorInst OrdInst self

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::max"]
def iter.traits.iterator.Iterator.max.default
    {Self Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (OrdInst : cmp.Ord Clause0_Item)
    (self : Self) : RustM (option.Option Clause0_Item) :=
  iter.traits.iterator.iter_max IteratorInst OrdInst self

/-! ## Lazy adapters kept OFF the `Iterator` structure — map / enumerate / step_by /
     take / skip / filter / filter_map / take_while / skip_while / map_while

These COULD be trait fields (their `.default` is instance-free or takes only a
closure `Fn` dictionary — no SELF instance), but making them fields forced a
`patch_lean.py` back-fill (`fill_iterator_default_fields`) onto the cross-crate
`alloc` `Iterator` instances. To keep the generated Lean un-patched we supply
them here as standalone `@[rust_fun]`-tagged functions instead, exactly like
rev/collect/zip/… . Bodies just build the adapter via its generated `::new`
(the unused `Fn` dictionaries mirror what aeneas threads through). -/
-- Signatures match aeneas's downstream emission `Iterator.<m>.default (IteratorInst)
-- [otherInsts] (self) [args]`, as pinned by the `iter_*` canary functions in
-- `tests/client_test/src/lib.rs`. `map`'s closure dictionary is `FnMut` (std uses FnMut), matching the
-- `Map` adapter's `FnMut` bound.
open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::map"]
def iter.traits.iterator.Iterator.map.default
    {Self O F Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_FnMutInst : core.ops.function.FnMut F Clause0_Item O)
    (self : Self) (f : F) : RustM (iter.adapters.map.Map Self F) :=
  iter.adapters.map.Map.new self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::enumerate"]
def iter.traits.iterator.Iterator.enumerate.default
    {Self Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) : RustM (iter.adapters.enumerate.Enumerate Self) :=
  iter.adapters.enumerate.Enumerate.new self

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::step_by"]
def iter.traits.iterator.Iterator.step_by.default
    {Self Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) (step : Aeneas.Std.Usize) :
    RustM (iter.adapters.step_by.StepBy Self) :=
  iter.adapters.step_by.StepBy.new self step

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::take"]
def iter.traits.iterator.Iterator.take.default
    {Self Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) (n : Aeneas.Std.Usize) :
    RustM (iter.adapters.take.Take Self) :=
  iter.adapters.take.Take.new self n

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::skip"]
def iter.traits.iterator.Iterator.skip.default
    {Self Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) (n : Aeneas.Std.Usize) :
    RustM (iter.adapters.skip.Skip Self) :=
  iter.adapters.skip.Skip.new self n

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::filter"]
def iter.traits.iterator.Iterator.filter.default
    {Self P Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_FnInst : core.ops.function.FnMut P Clause0_Item Bool)
    (self : Self) (predicate : P) : RustM (iter.adapters.filter.Filter Self P) :=
  iter.adapters.filter.Filter.new self predicate

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::filter_map"]
def iter.traits.iterator.Iterator.filter_map.default
    {Self B F Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_FnInst : core.ops.function.FnMut F Clause0_Item (option.Option B))
    (self : Self) (f : F) : RustM (iter.adapters.filter_map.FilterMap Self F) :=
  iter.adapters.filter_map.FilterMap.new self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::take_while"]
def iter.traits.iterator.Iterator.take_while.default
    {Self P Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_FnInst : core.ops.function.FnMut P Clause0_Item Bool)
    (self : Self) (predicate : P) :
    RustM (iter.adapters.take_while.TakeWhile Self P) :=
  iter.adapters.take_while.TakeWhile.new self predicate

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::skip_while"]
def iter.traits.iterator.Iterator.skip_while.default
    {Self P Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_FnInst : core.ops.function.FnMut P Clause0_Item Bool)
    (self : Self) (predicate : P) :
    RustM (iter.adapters.skip_while.SkipWhile Self P) :=
  iter.adapters.skip_while.SkipWhile.new self predicate

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::map_while"]
def iter.traits.iterator.Iterator.map_while.default
    {Self B F Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_FnInst : core.ops.function.FnMut F Clause0_Item (option.Option B))
    (self : Self) (f : F) : RustM (iter.adapters.map_while.MapWhile Self F) :=
  iter.adapters.map_while.MapWhile.new self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::inspect"]
def iter.traits.iterator.Iterator.inspect.default
    {Self F Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (_FnInst : core.ops.function.FnMut F Clause0_Item Unit)
    (self : Self) (f : F) : RustM (iter.adapters.inspect.Inspect Self F) :=
  iter.adapters.inspect.Inspect.new self f

open Aeneas.Std (RustM) in
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fuse"]
def iter.traits.iterator.Iterator.fuse.default
    {Self Clause0_Item : Type}
    (_IteratorInst : iter.traits.iterator.Iterator Self Clause0_Item)
    (self : Self) :
    RustM (iter.adapters.fuse.Fuse Self) :=
  iter.adapters.fuse.Fuse.new self

/-! ## `slice::iter_mut` / `IterMut` — the &mut-yielding slice iterator (opaque model)

`IterMut` yields `&mut T`, so its `next` returns a 3-tuple `(Option T) × Self ×
(Self → Option T → Self)` — the third component writes the (possibly-modified)
element back. This can't be an `Iterator` trait instance (2-tuple `next`), so the
extraction calls this specialised `next` directly (as with Aeneas.Std's
`SliceIter`). Bodies mirror Aeneas.Std, adapted to `core.option.Option`. -/
open Aeneas.Std in
def slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.next {T : Type}
    (it : slice.iter.IterMut T) :
    Aeneas.Std.RustM ((option.Option T) × (slice.iter.IterMut T) ×
      (slice.iter.IterMut T → option.Option T → slice.iter.IterMut T)) :=
  if h : it.i < it.slice.length then
    let x := it.slice[it.i]
    let i := it.i
    let it := { it with i := i + 1 }
    let back := fun (it' : slice.iter.IterMut T) (o : option.Option T) =>
      match o with
      | option.Option.None => it'
      | option.Option.Some x => { it' with slice := it'.slice.setAtNat i x }
    .ok (option.Option.Some x, it, back)
  else .ok (option.Option.None, it, fun it' _ => it')

open Aeneas.Std in
def slice.Slice.iter_mut {T : Type} (s : Aeneas.Std.Slice T) :
    Aeneas.Std.RustM ((slice.iter.IterMut T) ×
      (slice.iter.IterMut T → Aeneas.Std.Slice T)) :=
  .ok ({ slice := s, i := 0 }, fun it => it.slice)

/-! ## `str::as_bytes`

`Str` is definitionally `Slice U8` (Aeneas.Std `StringDef`), so `str::as_bytes` is
the identity on the underlying bytes — faithful, no opacity, no trust expansion.
(The verify path passes a domain-separator `label : Str` to `Transcript::new`.) -/
open Aeneas.Std in
def str.Str.as_bytes (s : Str) : Aeneas.Std.RustM (Slice U8) :=
  .ok s

/-! ## Per-impl specialisations of the eager consumers

Aeneas emits the *generic* `Iterator.<m>.default` for the lazy adapter
constructors, but a *per-impl specialisation* `<Receiver>.Insts.<Inst>.<m>` for
the eager consumers (`count`, `fold`, `last`, `min`, `max`) whenever the
receiver type is concrete. Each specialisation is just the generic default with
that receiver's own instance applied, so they are one-liners — but there is one
per (receiver, consumer) pair a client actually uses, so this set grows with
downstream code rather than being closed. The same consumers on a *polymorphic*
receiver are emitted as `Iterator` record-field projections instead, which this
model cannot serve; see the `poly_*` notes in `tests/client_test/src/lib.rs`.

Argument order is always: the instance's own dictionaries, then the consumer's
extra dictionaries, then `self`, then the consumer's remaining arguments — so
partial application plus eta is enough. -/

-- Range<A>
-- (`…IteratorIterator.count` is NOT defined here: `FunsPrologue.lean` already
-- provides it, derived from `Step::steps_between` instead of driving `next`.)
abbrev ops.range.Range.Insts.CoreIterTraitsIteratorIterator.last
    {A : Type} (StepInst : iter.range.Step A) :=
  iter.traits.iterator.Iterator.last.default
    (ops.range.Range.Insts.CoreIterTraitsIteratorIterator StepInst)

abbrev ops.range.Range.Insts.CoreIterTraitsIteratorIterator.min
    {A : Type} (StepInst : iter.range.Step A) :=
  iter.traits.iterator.Iterator.min.default
    (ops.range.Range.Insts.CoreIterTraitsIteratorIterator StepInst)

abbrev ops.range.Range.Insts.CoreIterTraitsIteratorIterator.max
    {A : Type} (StepInst : iter.range.Step A) :=
  iter.traits.iterator.Iterator.max.default
    (ops.range.Range.Insts.CoreIterTraitsIteratorIterator StepInst)

-- slice::Iter<T>
abbrev slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.count
    {T : Type} :=
  iter.traits.iterator.Iterator.count.default
    (slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)

abbrev slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
    {T B F : Type}
    (FoldFnInst : core.ops.function.FnMut F (B × T) B) :=
  iter.traits.iterator.Iterator.fold.default
    (slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T) FoldFnInst

-- Map<I, F>
abbrev iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.fold
    {I O F Clause0_Item B G : Type}
    (IteratorInst : iter.traits.iterator.Iterator I Clause0_Item)
    (FnMutInst : core.ops.function.FnMut F Clause0_Item O)
    (FoldFnInst : core.ops.function.FnMut G (B × O) B) :=
  iter.traits.iterator.Iterator.fold.default
    (iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator IteratorInst FnMutInst)
    FoldFnInst

-- Enumerate<I>
abbrev iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.fold
    {I Clause0_Item B G : Type}
    (IteratorInst : iter.traits.iterator.Iterator I Clause0_Item)
    (FoldFnInst : core.ops.function.FnMut G (B × (Aeneas.Std.Usize × Clause0_Item)) B) :=
  iter.traits.iterator.Iterator.fold.default
    (iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
      IteratorInst) FoldFnInst

-- Skip<I>
abbrev iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.count
    {I Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator I Clause0_Item) :=
  iter.traits.iterator.Iterator.count.default
    (iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator IteratorInst)

-- Fuse<I>
abbrev iter.adapters.fuse.Fuse.Insts.CoreIterTraitsIteratorIterator.count
    {I Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator I Clause0_Item) :=
  iter.traits.iterator.Iterator.count.default
    (iter.adapters.fuse.Fuse.Insts.CoreIterTraitsIteratorIterator IteratorInst)

-- Filter<I, P>
abbrev iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.count
    {I P Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator I Clause0_Item)
    (FnMutInst : core.ops.function.FnMut P Clause0_Item Bool) :=
  iter.traits.iterator.Iterator.count.default
    (iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator IteratorInst FnMutInst)

-- Chain<A, B>
abbrev iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.count
    {A B Clause0_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator A Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator B Clause0_Item) :=
  iter.traits.iterator.Iterator.count.default
    (iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator IteratorInst IteratorInst1)

-- Flatten<I, _, _>
abbrev iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.count
    {I Clause0_Item Clause1_Item : Type}
    (IteratorInst : iter.traits.iterator.Iterator I Clause0_Item)
    (IteratorInst1 : iter.traits.iterator.Iterator Clause0_Item Clause1_Item) :=
  iter.traits.iterator.Iterator.count.default
    (iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator
      IteratorInst IteratorInst1)


end core

namespace alloc

/-! ## `IntoIterator` for `&Vec<T>` (aeneas's `SharedAVec`)

`(&vec).into_iter()` / iterating a `&Vec<T>` yields `&T` via a slice `Iter`. aeneas
names this shared-reference `IntoIterator` instance `alloc.SharedAVec.Insts.
CoreIterTraitsCollectIntoIteratorSharedATIter` (cf. Aeneas.Std's `SharedArray` for
`&[T; N]`). Core-models didn't provide it; supply `into_iter` by hand —
`Vec::as_slice` then the slice `Iter` constructor — matching the name/signature the
extraction calls directly. -/
open Aeneas.Std (RustM) in
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} (v : vec.Vec T) : RustM (core.slice.iter.Iter T) := do
  let s ← vec.Vec.as_slice v
  core.slice.Slice.iter s

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
  Aeneas.Std.RustM (core.iter.adapters.map.Map (vec.into_iter.IntoIter T) F) :=
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
  T_1 → Aeneas.Std.RustM (VecDeque T alloc.Global)

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
open Aeneas.Std (RustM) in
def vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop
    {T IntoIter : Type}
    (iterInst : core.iter.traits.iterator.Iterator IntoIter T)
    (it : IntoIter) (res : vec.Vec T) : RustM (vec.Vec T) := do
  let (o, it1) ← iterInst.next it
  match o with
  | core.option.Option.None => .ok res
  | core.option.Option.Some x =>
    let res1 ← vec.Vec.push res x
    vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop iterInst it1 res1
partial_fixpoint

open Aeneas.Std (RustM) in
def vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter
    {T I IntoIter : Type}
    (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter)
    (iter : I) : RustM (vec.Vec T) := do
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
  Aeneas.Std.RustM (vec.Vec T) :=
  slice.Dummy.to_vec cloneInst s

@[rust_fun "alloc::slice::{alloc::boxed::Box<[@T], @A>}::into_vec"]
def slice.Slice.into_vec
  {T : Type} (s : Aeneas.Std.Slice T) : Aeneas.Std.RustM (vec.Vec T) :=
  slice.Dummy.into_vec s

end

end alloc
end CoreModels
