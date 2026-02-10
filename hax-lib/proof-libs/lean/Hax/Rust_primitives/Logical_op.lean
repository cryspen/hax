import Hax.Tactic.Init
import Hax.Rust_primitives.RustM

/-
  Logic predicates introduced by Hax (in pre/post conditions)
-/
section Logic

namespace rust_primitives.hax.Logical_op

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
@[inherit_doc] notation:max "!?" b:40 => not b

end rust_primitives.hax.Logical_op

end Logic
