import Hax.Rust_primitives.Tuple
import Hax.Rust_primitives.RustM

open Rust_primitives.Hax

namespace Hax_lib

abbrev assert (b:Bool) : RustM Tuple0 :=
  if b then pure ⟨ ⟩
  else .fail (Error.assertionFailure)

abbrev assume : Prop -> RustM Tuple0 := fun _ => pure ⟨ ⟩

abbrev Prop.Constructors.from_bool (b : Bool) : Prop := (b = true)

abbrev Prop.Impl.from_bool (b : Bool) : Prop := (b = true)

abbrev Prop.Constructors.implies (a b : Prop) : Prop := a → b

end Hax_lib
