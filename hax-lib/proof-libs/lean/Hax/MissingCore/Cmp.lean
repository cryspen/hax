import Hax.Rust_primitives

class core.cmp.PartialEq.AssociatedTypes (Self : Type) (Rhs : Type) where

class core.cmp.PartialEq (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialEq.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  eq : (Self -> Rhs -> RustM Bool)

@[reducible]
instance {α} [BEq α] : core.cmp.PartialEq.AssociatedTypes α α := ⟨⟩

instance {α} [BEq α] : core.cmp.PartialEq α α := ⟨fun a b => a == b⟩
