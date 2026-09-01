/- Discharges the obligations that `Extraction/ProofObligations.lean` states
with `sorry`: every `#[spec(..)]` in `src/lib.rs` holds, whether it was written
with `anodized` or with `hax_lib` directly. -/
import Anodized.Extraction
import Hax
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace anodized_example

theorem f1.spec.proof (x : Std.U8) : f1.spec x := by
  unfold spec; intro _; hax_mvcgen

theorem f2.spec.proof (x : Std.U8) : f2.spec x := by
  unfold spec; intro _; hax_mvcgen

theorem f3.spec.proof (x : Std.U8) : f3.spec x := by
  unfold spec post; hax_mvcgen [f3]

theorem f4.spec.proof (x : Std.U8) : f4.spec x := by
  unfold spec post; hax_mvcgen [f4]

theorem f5.spec.proof (x : Std.U8) : f5.spec x := by
  unfold spec post; hax_mvcgen [f5]

theorem f6.spec.proof (x : Std.U8) : f6.spec x := by
  unfold spec post; intro _; hax_mvcgen [f6]

end anodized_example
