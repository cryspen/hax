import Hax.MissingCore.Clone

class core.marker.Copy.AssociatedTypes (Self : Type) where

class core.marker.Copy
  (Self : Type)
  [associatedTypes : outParam (core.marker.Copy.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr : core.clone.Clone Self]

attribute [instance] core.marker.Copy.trait_constr
