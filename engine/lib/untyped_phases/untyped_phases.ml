
open Prelude
    
module type PHASE_FULL =
  Phase_utils.PHASE
    with module FA = Features.Full
     and module FB = Features.Full
     and module A = Ast.Full
     and module B = Ast.Full

module BindPhaseFull (A : PHASE_FULL) (B : PHASE_FULL) : PHASE_FULL = struct
  include Phase_utils.BindPhase (A) (B)
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full
end

module IdentityFull : PHASE_FULL = struct
  include Phase_utils.Identity (Features.Full)
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full
end

let bind (module A : PHASE_FULL) (module B : PHASE_FULL) : (module PHASE_FULL) =
  (module BindPhaseFull (A) (B))

let bind_list : (module PHASE_FULL) list -> (module PHASE_FULL) =
  List.reduce ~f:bind
  >> Option.value ~default:(module IdentityFull : PHASE_FULL)



module And_mut_defsite : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    include On.Mutable_variable
include On.Mutable_reference
include On.Nontrivial_lhs
include On.Arbitrary_lhs
include On.Reference
  end

  module Phase = Phases.And_mut_defsite (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        let mutable_variable = fun _ _ -> Features.On.mutable_variable
let mutable_reference = fun _ _ -> Features.On.mutable_reference
let nontrivial_lhs = fun _ _ -> Features.On.nontrivial_lhs
let arbitrary_lhs = fun _ _ -> Features.On.arbitrary_lhs
let reference = fun _ _ -> Features.On.reference

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Bundle_cycles : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Bundle_cycles (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Cf_into_monads : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    include Off.Monadic_action
include Off.Monadic_binding
  end

  module Phase = Phases.Cf_into_monads (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        let monadic_action = reject
let monadic_binding = reject

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Direct_and_mut : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    include Off.Raw_pointer
include Off.Mutable_pointer
  end

  module Phase = Phases.Direct_and_mut (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        let raw_pointer = reject
let mutable_pointer = reject

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Drop_blocks : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Drop_blocks (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Drop_match_guards : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Drop_match_guards (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Drop_references : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    include Off.Raw_pointer
include Off.Mutable_reference
  end

  module Phase = Phases.Drop_references (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        let raw_pointer = reject
let mutable_reference = reject

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Drop_return_break_continue : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Drop_return_break_continue (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Drop_sized_trait : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Drop_sized_trait (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Functionalize_loops : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    include Off.Continue
include Off.Early_exit
include Off.Break
  end

  module Phase = Phases.Functionalize_loops (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        let continue = reject
let early_exit = reject
let break = reject

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Hoist_disjunctive_patterns : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Hoist_disjunctive_patterns (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Local_mutation : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    include Off.Mutable_reference
include Off.Mutable_pointer
include Off.Raw_pointer
include Off.Arbitrary_lhs
include Off.Nontrivial_lhs
include Off.Monadic_action
include Off.Monadic_binding
include Off.For_index_loop
  end

  module Phase = Phases.Local_mutation (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        let mutable_reference = reject
let mutable_pointer = reject
let raw_pointer = reject
let arbitrary_lhs = reject
let nontrivial_lhs = reject
let monadic_action = reject
let monadic_binding = reject
let for_index_loop = reject

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Newtype_as_refinement : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Newtype_as_refinement (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Reconstruct_asserts : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Reconstruct_asserts (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Reconstruct_for_index_loops : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Reconstruct_for_index_loops (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Reconstruct_for_loops : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Reconstruct_for_loops (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Reconstruct_question_marks : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Reconstruct_question_marks (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Reconstruct_while_loops : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Reconstruct_while_loops (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Reorder_fields : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Reorder_fields (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Rewrite_control_flow : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Rewrite_control_flow (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Simplify_hoisting : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Simplify_hoisting (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Simplify_match_return : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Simplify_match_return (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Simplify_question_marks : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Simplify_question_marks (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Sort_items : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Sort_items (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Specialize : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Specialize (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Traits_specs : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Traits_specs (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Transform_hax_lib_inline : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Transform_hax_lib_inline (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end


module Trivialize_assign_lhs : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    
  end

  module Phase = Phases.Trivialize_assign_lhs (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end

let and_mut_defsite : (module PHASE_FULL) = (module And_mut_defsite)
let bundle_cycles : (module PHASE_FULL) = (module Bundle_cycles)
let cf_into_monads : (module PHASE_FULL) = (module Cf_into_monads)
let direct_and_mut : (module PHASE_FULL) = (module Direct_and_mut)
let drop_blocks : (module PHASE_FULL) = (module Drop_blocks)
let drop_match_guards : (module PHASE_FULL) = (module Drop_match_guards)
let drop_references : (module PHASE_FULL) = (module Drop_references)
let drop_return_break_continue : (module PHASE_FULL) = (module Drop_return_break_continue)
let drop_sized_trait : (module PHASE_FULL) = (module Drop_sized_trait)
let functionalize_loops : (module PHASE_FULL) = (module Functionalize_loops)
let hoist_disjunctive_patterns : (module PHASE_FULL) = (module Hoist_disjunctive_patterns)
let local_mutation : (module PHASE_FULL) = (module Local_mutation)
let newtype_as_refinement : (module PHASE_FULL) = (module Newtype_as_refinement)
let reconstruct_asserts : (module PHASE_FULL) = (module Reconstruct_asserts)
let reconstruct_for_index_loops : (module PHASE_FULL) = (module Reconstruct_for_index_loops)
let reconstruct_for_loops : (module PHASE_FULL) = (module Reconstruct_for_loops)
let reconstruct_question_marks : (module PHASE_FULL) = (module Reconstruct_question_marks)
let reconstruct_while_loops : (module PHASE_FULL) = (module Reconstruct_while_loops)
let reorder_fields : (module PHASE_FULL) = (module Reorder_fields)
let rewrite_control_flow : (module PHASE_FULL) = (module Rewrite_control_flow)
let simplify_hoisting : (module PHASE_FULL) = (module Simplify_hoisting)
let simplify_match_return : (module PHASE_FULL) = (module Simplify_match_return)
let simplify_question_marks : (module PHASE_FULL) = (module Simplify_question_marks)
let sort_items : (module PHASE_FULL) = (module Sort_items)
let specialize : (module PHASE_FULL) = (module Specialize)
let traits_specs : (module PHASE_FULL) = (module Traits_specs)
let transform_hax_lib_inline : (module PHASE_FULL) = (module Transform_hax_lib_inline)
let trivialize_assign_lhs : (module PHASE_FULL) = (module Trivialize_assign_lhs)
let phases_list : (module PHASE_FULL) list = [and_mut_defsite;bundle_cycles;cf_into_monads;direct_and_mut;drop_blocks;drop_match_guards;drop_references;drop_return_break_continue;drop_sized_trait;functionalize_loops;hoist_disjunctive_patterns;local_mutation;newtype_as_refinement;reconstruct_asserts;reconstruct_for_index_loops;reconstruct_for_loops;reconstruct_question_marks;reconstruct_while_loops;reorder_fields;rewrite_control_flow;simplify_hoisting;simplify_match_return;simplify_question_marks;sort_items;specialize;traits_specs;transform_hax_lib_inline;trivialize_assign_lhs]

let phase_of_name: string -> (module PHASE_FULL) option = 
    function
    | "and_mut_defsite" -> Some and_mut_defsite| "bundle_cycles" -> Some bundle_cycles| "cf_into_monads" -> Some cf_into_monads| "direct_and_mut" -> Some direct_and_mut| "drop_blocks" -> Some drop_blocks| "drop_match_guards" -> Some drop_match_guards| "drop_references" -> Some drop_references| "drop_return_break_continue" -> Some drop_return_break_continue| "drop_sized_trait" -> Some drop_sized_trait| "functionalize_loops" -> Some functionalize_loops| "hoist_disjunctive_patterns" -> Some hoist_disjunctive_patterns| "local_mutation" -> Some local_mutation| "newtype_as_refinement" -> Some newtype_as_refinement| "reconstruct_asserts" -> Some reconstruct_asserts| "reconstruct_for_index_loops" -> Some reconstruct_for_index_loops| "reconstruct_for_loops" -> Some reconstruct_for_loops| "reconstruct_question_marks" -> Some reconstruct_question_marks| "reconstruct_while_loops" -> Some reconstruct_while_loops| "reorder_fields" -> Some reorder_fields| "rewrite_control_flow" -> Some rewrite_control_flow| "simplify_hoisting" -> Some simplify_hoisting| "simplify_match_return" -> Some simplify_match_return| "simplify_question_marks" -> Some simplify_question_marks| "sort_items" -> Some sort_items| "specialize" -> Some specialize| "traits_specs" -> Some traits_specs| "transform_hax_lib_inline" -> Some transform_hax_lib_inline| "trivialize_assign_lhs" -> Some trivialize_assign_lhs
    | _ -> None

let phases: string list = ["and_mut_defsite";"bundle_cycles";"cf_into_monads";"direct_and_mut";"drop_blocks";"drop_match_guards";"drop_references";"drop_return_break_continue";"drop_sized_trait";"functionalize_loops";"hoist_disjunctive_patterns";"local_mutation";"newtype_as_refinement";"reconstruct_asserts";"reconstruct_for_index_loops";"reconstruct_for_loops";"reconstruct_question_marks";"reconstruct_while_loops";"reorder_fields";"rewrite_control_flow";"simplify_hoisting";"simplify_match_return";"simplify_question_marks";"sort_items";"specialize";"traits_specs";"transform_hax_lib_inline";"trivialize_assign_lhs"]

