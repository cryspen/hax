module Tests.Legacy__traits.Block_size
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_BlockSizeUser (v_Self: Type0) = { f_BlockSize:Type0 }

class t_ParBlocksSizeUser (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_BlockSizeUser v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_ParBlocksSizeUser v_Self|} -> i._super_i0

class t_BlockBackend (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_ParBlocksSizeUser v_Self;
  f_proc_block_pre:Alloc.Vec.t_Vec _ Alloc.Alloc.t_Global -> Type0;
  f_proc_block_post:Alloc.Vec.t_Vec _ Alloc.Alloc.t_Global -> Prims.unit -> Type0;
  f_proc_block:x0: Alloc.Vec.t_Vec _ Alloc.Alloc.t_Global
    -> Prims.Pure Prims.unit (f_proc_block_pre x0) (fun result -> f_proc_block_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_BlockBackend v_Self|} -> i._super_i0
