import Hax.rust_primitives.RustM
import Hax.rust_primitives.USize64
import Hax.rust_primitives.num

open Std.Do
set_option mvcgen.warning false

namespace rust_primitives.hax.int

open Lean.Grind in
abbrev from_machine {α} {range} [ToInt α range] (x : α) : RustM Int :=
  pure (ToInt.toInt x)

attribute [grind]
  Lean.Grind.ToInt.toInt
  Lean.Grind.instToIntUInt8UintOfNatNat
  Lean.Grind.instToIntUInt16UintOfNatNat
  Lean.Grind.instToIntUInt32UintOfNatNat
  Lean.Grind.instToIntUInt64UintOfNatNat
  Lean.Grind.instToIntUSize64UintOfNatNat
  Lean.Grind.instToIntInt8SintOfNatNat
  Lean.Grind.instToIntInt16SintOfNatNat
  Lean.Grind.instToIntInt32SintOfNatNat
  Lean.Grind.instToIntInt64SintOfNatNat
  Lean.Grind.instToIntISizeSintNumBits

@[spec] def add (x y : Int) : RustM Int := pure (x + y)
@[spec] def sub (x y : Int) : RustM Int := pure (x - y)
@[spec] def mul (x y : Int) : RustM Int := pure (x * y)
@[spec] def div (x y : Int) : RustM Int :=
  if y == 0 then
    .fail .divisionByZero
  else
    pure (x / y)
@[spec] def neg (x : Int) : RustM Int := pure (-x)
@[spec] def gt (x y : Int) : RustM Bool := pure (x > y)
@[spec] def lt (x y : Int) : RustM Bool := pure (x < y)
@[spec] def ge (x y : Int) : RustM Bool := pure (x ≥ y)
@[spec] def le (x y : Int) : RustM Bool := pure (x ≤ y)
@[spec] def eq (x y : Int) : RustM Bool := pure (x == y)

end rust_primitives.hax.int
