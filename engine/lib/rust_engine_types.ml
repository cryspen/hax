(** This module re-exports and renames a subset of `Types`.
    `Types` contains both the modules from the frontend and from the Rust engine.
    Thus, some types are deduplicated, and get renamed.
*)

module Renamed = struct
  type arm = Types.arm2
  type attribute = Types.attribute2
  type attribute_kind = Types.attribute_kind2
  type binding_mode = Types.binding_mode2
  type borrow_kind = Types.borrow_kind2
  type def_id = Types.def_id2
  type expr_kind = Types.expr_kind2
  type impl_expr = Types.impl_expr2
  type param = Types.param2
  type pat_kind = Types.pat_kind2
  type projection_predicate = Types.projection_predicate2
  type region = Types.region2
  type span = Types.span2
end

include Types
include Renamed
