
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

--  Values having this type hold a representative 'x' of the Kyber field.
--  We use 'fe' as a shorthand for this type.
abbrev Lean_barrett.FieldElement : Type := i32

@[simp, spec]

def Lean_barrett.BARRETT_R : i64 :=
  RustM.of_isOk (do (pure (4194304 : i64))) (by rfl)

@[simp, spec]

def Lean_barrett.BARRETT_SHIFT : i64 :=
  RustM.of_isOk (do (pure (26 : i64))) (by rfl)

@[simp, spec]

def Lean_barrett.BARRETT_MULTIPLIER : i64 :=
  RustM.of_isOk (do (pure (20159 : i64))) (by rfl)

@[simp, spec]

def Lean_barrett.FIELD_MODULUS : i32 :=
  RustM.of_isOk (do (pure (3329 : i32))) (by rfl)

def Lean_barrett.barrett_reduce_precondition (value : i32) : RustM Bool := do
  ((← (Rust_primitives.Hax.Machine_int.ge
      (← (Core.Convert.From.from i64 i32 value))
      (← (Core.Ops.Arith.Neg.neg Lean_barrett.BARRETT_R))))
    &&? (← (Rust_primitives.Hax.Machine_int.le
      (← (Core.Convert.From.from i64 i32 value))
      Lean_barrett.BARRETT_R)))

def Lean_barrett.barret_reduce_postcondition
  (value : i32)
  (result : i32)
  : RustM Bool
  := do
  let valid_result : i32 ← (value %? Lean_barrett.FIELD_MODULUS);
  ((← ((← (Rust_primitives.Hax.Machine_int.gt
        result
        (← (Core.Ops.Arith.Neg.neg Lean_barrett.FIELD_MODULUS))))
      &&? (← (Rust_primitives.Hax.Machine_int.lt
        result
        Lean_barrett.FIELD_MODULUS))))
    &&? (← ((← ((← (Rust_primitives.Hax.Machine_int.eq result valid_result))
        ||? (← (Rust_primitives.Hax.Machine_int.eq
          result
          (← (valid_result +? Lean_barrett.FIELD_MODULUS))))))
      ||? (← (Rust_primitives.Hax.Machine_int.eq
        result
        (← (valid_result -? Lean_barrett.FIELD_MODULUS)))))))

--  Signed Barrett Reduction
-- 
--  Given an input `value`, `barrett_reduce` outputs a representative `result`
--  such that:
-- 
--  - result ≡ value (mod FIELD_MODULUS)
--  - the absolute value of `result` is bound as follows:
-- 
--  `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
-- 
--  In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
def Lean_barrett.barrett_reduce (value : i32) : RustM i32 := do
  let t : i64 ←
    ((← (Core.Convert.From.from i64 i32 value))
      *? Lean_barrett.BARRETT_MULTIPLIER);
  let t : i64 ← (t +? (← (Lean_barrett.BARRETT_R >>>? (1 : i32))));
  let quotient : i64 ← (t >>>? Lean_barrett.BARRETT_SHIFT);
  let quotient : i32 ← (Rust_primitives.Hax.cast_op quotient);
  let sub : i32 ← (quotient *? Lean_barrett.FIELD_MODULUS);
  (value -? sub)


set_option maxHeartbeats 1000000 in
-- quite computation intensive
theorem barrett_spec (value: i32) :
  ⦃ ⌜ Lean_barrett.barrett_reduce_precondition (value) = pure true ⌝ ⦄
  Lean_barrett.barrett_reduce value
  ⦃ ⇓ r => ⌜ Lean_barrett.barret_reduce_postcondition value r = pure true⌝ ⦄
:= by
  -- Unfold all auxiliary functions:
  unfold
    Lean_barrett.barrett_reduce Lean_barrett.barrett_reduce_precondition
    Lean_barrett.barret_reduce_postcondition
    Lean_barrett.FIELD_MODULUS Lean_barrett.BARRETT_R
    Lean_barrett.BARRETT_MULTIPLIER Lean_barrett.BARRETT_SHIFT at *
  -- Invoke bit blasting:
  hax_bv_decide (timeout := 60)