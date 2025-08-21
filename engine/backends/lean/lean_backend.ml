open Hax_engine
open Utils
open Base

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Monadic_binding
      include On.Slice
      include On.Macro
      include On.Construct_base
      include On.Quote
      include On.Dyn
      include On.Unsafe
    end)
    (struct
      let backend = Diagnostics.Backend.FStar
    end)

module SubtypeToInputLanguage
    (FA :
      Features.T
        with type mutable_reference = Features.Off.mutable_reference
         and type continue = Features.Off.continue
         and type break = Features.Off.break
         and type mutable_reference = Features.Off.mutable_reference
         and type mutable_pointer = Features.Off.mutable_pointer
         and type mutable_variable = Features.Off.mutable_variable
         and type reference = Features.Off.reference
         and type raw_pointer = Features.Off.raw_pointer
         and type early_exit = Features.Off.early_exit
         and type question_mark = Features.Off.question_mark
         and type as_pattern = Features.Off.as_pattern
         and type lifetime = Features.Off.lifetime
         and type monadic_action = Features.Off.monadic_action
         and type arbitrary_lhs = Features.Off.arbitrary_lhs
         and type nontrivial_lhs = Features.Off.nontrivial_lhs
         and type loop = Features.Off.loop
         and type block = Features.Off.block
         and type for_loop = Features.Off.for_loop
         and type while_loop = Features.Off.while_loop
         and type for_index_loop = Features.Off.for_index_loop
         and type state_passing_loop = Features.Off.state_passing_loop
         and type fold_like_loop = Features.Off.fold_like_loop
         and type match_guard = Features.Off.match_guard
         and type trait_item_default = Features.Off.trait_item_default) =
struct
  module FB = InputLanguage

  include
    Subtype.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Features.SUBTYPE.Id
        include Features.SUBTYPE.On.Monadic_binding
        include Features.SUBTYPE.On.Construct_base
        include Features.SUBTYPE.On.Slice
        include Features.SUBTYPE.On.Macro
        include Features.SUBTYPE.On.Quote
        include Features.SUBTYPE.On.Dyn
        include Features.SUBTYPE.On.Unsafe
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module AST = Ast.Make (InputLanguage)

module BackendOptions = struct
  type t = Hax_engine.Types.f_star_options_for__null
end

open Ast
module U = Ast_utils.Make (InputLanguage)
module Visitors = Ast_visitors.Make (InputLanguage)
open AST

module Context = struct
  type t = {
    current_namespace : string list;
    items : item list;
    interface_mode : bool;
    line_width : int;
  }
end

open Phase_utils
module DepGraphR = Dependencies.Make (Features.Rust)

module TransformToInputLanguage =
  [%functor_application
    Phases.Reject.RawOrMutPointer(Features.Rust)
  |> Phases.Transform_hax_lib_inline
  |> Phases.Specialize
  |> Phases.Drop_sized_trait
  |> Phases.Simplify_question_marks
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_asserts
  |> Phases.Reconstruct_for_loops
  |> Phases.Reconstruct_while_loops
  |> Phases.Direct_and_mut
  |> Phases.Reject.Arbitrary_lhs
  |> Phases.Drop_blocks
  |> Phases.Drop_match_guards
  |> Phases.Drop_references
  |> Phases.Trivialize_assign_lhs
  |> Side_effect_utils.Hoist
  |> Phases.Hoist_disjunctive_patterns
  |> Phases.Simplify_match_return
  |> Phases.Local_mutation
  |> Phases.Rewrite_control_flow
  |> Phases.Drop_return_break_continue
  |> Phases.Functionalize_loops
  |> Phases.Reject.Question_mark
  |> Phases.Reject.As_pattern
  |> Phases.Traits_specs
  |> Phases.Simplify_hoisting
  |> Phases.Newtype_as_refinement
  |> Phases.Reject.Trait_item_default
  |> Phases.Bundle_cycles
  |> Phases.Reorder_fields
  |> Phases.Sort_items
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]

let apply_phases (items : Ast.Rust.item list) : AST.item list =
  TransformToInputLanguage.ditems items
