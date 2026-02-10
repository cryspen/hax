import Hax.Rust_primitives.Tuple
import Hax.Rust_primitives.RustM

open rust_primitives.hax

namespace hax_lib

abbrev assert (b:Bool) : RustM Tuple0 :=
  if b then pure ⟨ ⟩
  else .fail (Error.assertionFailure)

abbrev assume : Prop -> RustM Tuple0 := fun _ => pure ⟨ ⟩

abbrev prop.constructors.from_bool (b : Bool) : Prop := (b = true)

abbrev prop.Impl.from_bool (b : Bool) : Prop := (b = true)

abbrev prop.constructors.implies (a b : Prop) : Prop := a → b

end hax_lib
