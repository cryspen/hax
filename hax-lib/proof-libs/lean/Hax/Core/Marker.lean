import Hax.Core.Clone

class Core.Marker.Copy.AssociatedTypes (Self : Type) where

class Core.Marker.Copy
  (Self : Type)
  [associatedTypes : outParam (Core.Marker.Copy.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr : Core.Clone.Clone Self]

attribute [instance] Core.Marker.Copy.trait_constr
