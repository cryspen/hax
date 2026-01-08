import Hax.Integers.Ops
import Hax.Integers.Spec
import Hax.Float

namespace Rust_primitives.Hax

  abbrev Never : Type := Empty
  abbrev never_to_any.{u} {α : Sort u} : Never → α := Empty.elim

end Rust_primitives.Hax
