import Hax.Tactic.Init
import Hax.rust_primitives.RustM

/-
  Logic predicates introduced by Hax (in pre/post conditions)
-/
namespace rust_primitives.hax.logical_op

/-- Boolean conjunction. Cannot panic (always returns .ok ) -/
@[simp, spec, hax_bv_decide]
def and (a b: Bool) : RustM Bool := pure (a && b)

/-- Boolean disjunction. Cannot panic (always returns .ok )-/
@[simp, spec, hax_bv_decide]
def or (a b: Bool) : RustM Bool := pure (a || b)

/-- Boolean negation. Cannot panic (always returns .ok )-/
@[simp, spec, hax_bv_decide]
def not (a :Bool) : RustM Bool := pure (!a)

@[inherit_doc] infixl:35 " &&? " => and
@[inherit_doc] infixl:30 " ||? " => or
@[inherit_doc] infixl:30 " ^^? " => xor
@[inherit_doc] notation:max "!?" b:40 => not b

end rust_primitives.hax.logical_op

namespace rust_primitives.hax

@[spec] def logical_op_or (x y : Bool) : RustM Bool := pure (x || y)
@[spec] def logical_op_and (x y : Bool) : RustM Bool := pure (x && y)

end rust_primitives.hax
