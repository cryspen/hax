module Core_models.Iter.Sources.Fused
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0)
    : Core_models.Iter.Traits.Marker.t_FusedIterator (Core_models.Iter.Sources.Empty.t_Empty v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0)
    : Core_models.Iter.Traits.Marker.t_FusedIterator (Core_models.Iter.Sources.Once.t_Once v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
    : Core_models.Iter.Traits.Marker.t_FusedIterator (Core_models.Iter.Sources.Repeat.t_Repeat v_A) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
    : Core_models.Iter.Traits.Marker.t_FusedIterator
    (Core_models.Iter.Sources.Repeat_n.t_RepeatN v_A) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
    : Core_models.Iter.Traits.Marker.t_FusedIterator
    (Core_models.Iter.Sources.Successors.t_Successors v_T v_F) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }
