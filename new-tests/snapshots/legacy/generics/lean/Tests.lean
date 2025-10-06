
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

structure Tests.Legacy__generics.Impl_generics.Test where


def Tests.Legacy__generics.Impl_generics.Impl.set_ciphersuites
  (S : Type)
  (impl_IntoIterator_Item_=_S_ : Type)
  [(Core.Convert.AsRef S String)]
  [(Core.Iter.Traits.Collect.IntoIterator impl_IntoIterator_Item_=_S_)]
  [sorry]
  (self : Tests.Legacy__generics.Impl_generics.Test)
  (ciphers : impl_IntoIterator_Item_=_S_)
  : Result
  (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0)
  := do
  (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__generics.Impl_generics.Impl.set_alpn_protocols
  (S : Type)
  (impl_IntoIterator_Item_=_S_ : Type)
  [(Core.Convert.AsRef S String)]
  [(Core.Iter.Traits.Collect.IntoIterator impl_IntoIterator_Item_=_S_)]
  [sorry]
  (self : Tests.Legacy__generics.Impl_generics.Test)
  (_protocols : impl_IntoIterator_Item_=_S_)
  : Result
  (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0)
  := do
  (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)

structure Tests.Legacy__generics.Defaults_generics.Defaults
  (T : Type) sorry where
  _0 : sorry

def Tests.Legacy__generics.Defaults_generics.f
  (_ :
  (Tests.Legacy__generics.Defaults_generics.Defaults
    Rust_primitives.Hax.Tuple0
    (2 : usize)))
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__generics.Assoc_const_param.Test sorry where


def Tests.Legacy__generics.Assoc_const_param.Impl.A
  sorry : Result (Tests.Legacy__generics.Assoc_const_param.Test N)
  := do
  Tests.Legacy__generics.Assoc_const_param.Test.mk

def Tests.Legacy__generics.Assoc_const_param.test
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Tests.Legacy__generics.Assoc_const_param.Test (1 : usize))
  := do
  (← Tests.Legacy__generics.Assoc_const_param.Impl.A (1 : usize))

def Tests.Legacy__generics.dup
  (T : Type) [(Core.Clone.Clone T)] (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  (Rust_primitives.Hax.Tuple2.mk
    (← Core.Clone.Clone.clone x) (← Core.Clone.Clone.clone x))

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__generics.foo sorry (arr : sorry) : Result usize := do
  let acc : usize ← (pure (← LEN +? (9 : usize)));
  let acc : usize ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        LEN
        (fun acc _ => (do true : Result Bool))
        acc
        (fun acc i => (do (← acc +? (← arr[i]_?)) : Result usize))));
  acc

def Tests.Legacy__generics.repeat
  sorry (T : Type) [(Core.Marker.Copy T)] (x : T)
  : Result sorry
  := do
  (← Rust_primitives.Hax.repeat x LEN)

def Tests.Legacy__generics.f sorry (x : usize) : Result usize := do
  (← (← N +? N) +? x)

def Tests.Legacy__generics.call_f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  (← (← Tests.Legacy__generics.f (10 : usize) (3 : usize)) +? (3 : usize))

def Tests.Legacy__generics.g
  sorry (T : Type) [(Core.Convert.Into T sorry)] (arr : T)
  : Result usize
  := do
  (← (← Core.Option.Impl.unwrap_or usize
        (← Core.Iter.Traits.Iterator.Iterator.max
            (← Core.Iter.Traits.Collect.IntoIterator.into_iter
                (← Core.Convert.Into.into arr)))
        N)
    +? N)

def Tests.Legacy__generics.call_g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  (← (← Tests.Legacy__generics.g (3 : usize) (RustArray usize 3)
        #v[(42 : usize), (3 : usize), (49 : usize)])
    +? (3 : usize))

class Tests.Legacy__generics.Foo (Self : Type) where
  const_add sorry : Self -> Result usize

instance Tests.Legacy__generics.Impl : Tests.Legacy__generics.Foo usize where
  const_add sorry (self : usize) := do (← self +? N)

structure Tests.Legacy__generics.Bar where


def Tests.Legacy__generics.Impl_1.inherent_impl_generics
  (T : Type) sorry (x : sorry)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk