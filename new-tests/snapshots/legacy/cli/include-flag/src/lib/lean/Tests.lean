
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

structure Tests.Legacy__cli__include_flag__src__lib.Foo where


class Tests.Legacy__cli__include_flag__src__lib.Trait (Self : Type) where


instance Tests.Legacy__cli__include_flag__src__lib.Impl :
  Tests.Legacy__cli__include_flag__src__lib.Trait
  Tests.Legacy__cli__include_flag__src__lib.Foo
  where


--  Indirect dependencies
def Tests.Legacy__cli__include_flag__src__lib.main_a_a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_b_a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_c_a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_a_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_b_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_c_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_a_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

--  Direct dependencies
def Tests.Legacy__cli__include_flag__src__lib.main_a
  (T : Type) [(Tests.Legacy__cli__include_flag__src__lib.Trait T)] (x : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_a_a
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_a_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_a_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_b_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_b_a
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_b_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_b_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_c_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cli__include_flag__src__lib.main_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_c_a
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_c_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_c_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

--  Entrypoint
def Tests.Legacy__cli__include_flag__src__lib.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_a
        Tests.Legacy__cli__include_flag__src__lib.Foo
        Tests.Legacy__cli__include_flag__src__lib.Foo.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Legacy__cli__include_flag__src__lib.main_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk