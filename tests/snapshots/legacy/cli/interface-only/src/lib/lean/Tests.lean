
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

def Tests.Legacy__cli__interface_only__src__lib._.requires
  (x : u8)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.lt x (254 : u8))

def Tests.Legacy__cli__interface_only__src__lib.__1.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__cli__interface_only__src__lib.__1.ensures
  (x : u8)
  (r : (RustArray u8 4))
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.gt (← r[(0 : usize)]_?) x)

--  This item contains unsafe blocks and raw references, two features
--  not supported by hax. Thanks to the `-i` flag and the `+:`
--  modifier, `f` is still extractable as an interface.
-- 
--  Expressions within type are still extracted, as well as pre- and
--  post-conditions.
--  @fail(extraction): ssprove(HAX0008, HAX0008, HAX0008, HAX0008), coq(HAX0008, HAX0008, HAX0008, HAX0008), fstar(HAX0008, HAX0008, HAX0008, HAX0008)
--  @fail(extraction): proverif(HAX0008, HAX0008, HAX0008, HAX0008)
def Tests.Legacy__cli__interface_only__src__lib.f
  (x : u8)
  : Result (RustArray u8 4)
  := do
  (← Rust_primitives.Hax.failure
      "ExplicitRejection { reason: "a node of kind [Raw_pointer] have been found in the AST" }


Note: the error was labeled with context `reject_RawOrMutPointer`.
"
      "{
 let y: raw_pointer!() = { cast(x) };
 {
 let _: tuple0 = {
 {
 let _: tuple0 = {
 {
 let _: tuple0 = {
 std::io::stdio::e_print({
 let args: [core::fmt::rt::t_Argument<
 lifetime!(something),
 >; 1...")

structure Tests.Legacy__cli__interface_only__src__lib.Bar where


--  Non-inherent implementations are extracted, their bodies are not
--  dropped. This might be a bit surprising: see
--  https://github.com/hacspec/hax/issues/616.
instance Tests.Legacy__cli__interface_only__src__lib.Impl :
  Core.Convert.From
  Tests.Legacy__cli__interface_only__src__lib.Bar
  Rust_primitives.Hax.Tuple0
  where
  _from (⟨⟩ : Rust_primitives.Hax.Tuple0) := do
    Tests.Legacy__cli__interface_only__src__lib.Bar.mk

def Tests.Legacy__cli__interface_only__src__lib.Impl_1.from.from
  (_ : u8)
  : Result Tests.Legacy__cli__interface_only__src__lib.Bar
  := do
  Tests.Legacy__cli__interface_only__src__lib.Bar.mk

--  If you need to drop the body of a method, please hoist it:
instance Tests.Legacy__cli__interface_only__src__lib.Impl_1 :
  Core.Convert.From Tests.Legacy__cli__interface_only__src__lib.Bar u8
  where
  _from (x : u8) := do
    (← Tests.Legacy__cli__interface_only__src__lib.Impl_1.from.from x)

structure Tests.Legacy__cli__interface_only__src__lib.Holder (T : Type) where
  value : (Alloc.Vec.Vec T Alloc.Alloc.Global)

instance Tests.Legacy__cli__interface_only__src__lib.Impl_2 (T : Type) :
  Core.Convert.From
  (Tests.Legacy__cli__interface_only__src__lib.Holder T)
  Rust_primitives.Hax.Tuple0
  where
  _from (⟨⟩ : Rust_primitives.Hax.Tuple0) := do
    (Tests.Legacy__cli__interface_only__src__lib.Holder.mk
      (value := (← Alloc.Vec.Impl.new T Rust_primitives.Hax.Tuple0.mk)))

structure Tests.Legacy__cli__interface_only__src__lib.Param sorry where
  value : sorry

instance Tests.Legacy__cli__interface_only__src__lib.Impl_3 sorry :
  Core.Convert.From
  (Tests.Legacy__cli__interface_only__src__lib.Param SIZE)
  Rust_primitives.Hax.Tuple0
  where
  _from (⟨⟩ : Rust_primitives.Hax.Tuple0) := do
    (Tests.Legacy__cli__interface_only__src__lib.Param.mk
      (value := (← Rust_primitives.Hax.repeat (0 : u8) SIZE)))

def Tests.Legacy__cli__interface_only__src__lib.f_generic
  sorry (U : Type) (_x : U)
  : Result (Tests.Legacy__cli__interface_only__src__lib.Param X)
  := do
  (Tests.Legacy__cli__interface_only__src__lib.Param.mk
    (value := (← Rust_primitives.Hax.repeat (0 : u8) X)))

class Tests.Legacy__cli__interface_only__src__lib.T (Self : Type) where
  Assoc : Type
  d : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0

--  Impls with associated types are not erased
instance Tests.Legacy__cli__interface_only__src__lib.Impl_4 :
  Tests.Legacy__cli__interface_only__src__lib.T u8
  where
  Assoc := u8
  d (_ : Rust_primitives.Hax.Tuple0) := do Rust_primitives.Hax.Tuple0.mk

class Tests.Legacy__cli__interface_only__src__lib.T2 (Self : Type) where
  d : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0

def Tests.Legacy__cli__interface_only__src__lib.Impl_5.d._.requires
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  false

--  Items can be forced to be transparent
instance Tests.Legacy__cli__interface_only__src__lib.Impl_5 :
  Tests.Legacy__cli__interface_only__src__lib.T2 u8
  where
  d (_ : Rust_primitives.Hax.Tuple0) := do Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__interface_only__src__lib.__2.requires
  (b : (RustSlice u8))
  (n : usize)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.ge (← Core.Slice.Impl.len u8 b) n)

def Tests.Legacy__cli__interface_only__src__lib.__3.future
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 T T)
  := do
  let hax_temp_output : T ← (pure x);
  (Rust_primitives.Hax.Tuple2.mk x hax_temp_output)

def Tests.Legacy__cli__interface_only__src__lib.__3.ensures
  (b : (RustSlice u8))
  (n : usize)
  (out : usize)
  : Result Bool
  := do
  (← Rust_primitives.Hax.Machine_int.le out n)

def Tests.Legacy__cli__interface_only__src__lib.padlen
  (b : (RustSlice u8))
  (n : usize)
  : Result usize
  := do
  (← if
  (← (← Rust_primitives.Hax.Machine_int.gt n (0 : usize))
    &&? (← Rust_primitives.Hax.Machine_int.eq
        (← b[(← n -? (1 : usize))]_?)
        (0 : u8))) then do
    (← (1 : usize)
      +? (← Tests.Legacy__cli__interface_only__src__lib.padlen
          b
          (← n -? (1 : usize))))
  else do
    (0 : usize))