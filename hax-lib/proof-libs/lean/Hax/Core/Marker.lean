/-
Hax Lean Backend - Cryspen

Core-model for Marker.Copy
-/

import Hax.Core.Clone
open Rust_primitives.Hax

class Core.Marker.Copy.AssociatedTypes (Self : Type) where
  [trait_constr_Copy_i0 : Core.Clone.Clone.AssociatedTypes Self]

attribute [instance]
  Core.Marker.Copy.AssociatedTypes.trait_constr_Copy_i0

class Core.Marker.Copy
  (Self : Type)
  [associatedTypes : outParam (Core.Marker.Copy.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_Copy_i0 : Core.Clone.Clone Self]

attribute [instance] Core.Marker.Copy.trait_constr_Copy_i0
