module Tests.Legacy__attributes.Refined_indexes
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_MAX: usize = mk_usize 10

type t_MyArray = | MyArray : t_Array u8 (mk_usize 10) -> t_MyArray

/// Triple dash comment
(** Multiline double star comment Maecenas blandit accumsan feugiat.
    Done vitae ullamcorper est.
    Curabitur id dui eget sem viverra interdum. *)
let mutation_example
      (uuse_generic_update_at: t_MyArray)
      (uuse_specialized_update_at: t_Slice u8)
      (specialized_as_well: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : (t_MyArray & t_Slice u8 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  let uuse_generic_update_at:t_MyArray =
    Rust_primitives.Hax.update_at uuse_generic_update_at (mk_usize 2) (mk_u8 0)
  in
  let uuse_specialized_update_at:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize uuse_specialized_update_at
      (mk_usize 2)
      (mk_u8 0)
  in
  let specialized_as_well:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize specialized_as_well
      (mk_usize 2)
      (mk_u8 0)
  in
  uuse_generic_update_at, uuse_specialized_update_at, specialized_as_well
  <:
  (t_MyArray & t_Slice u8 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Index.t_Index t_MyArray usize =
  {
    f_Output = u8;
    f_index_pre = (fun (self_: t_MyArray) (index: usize) -> index <. v_MAX);
    f_index_post = (fun (self: t_MyArray) (index: usize) (out: u8) -> true);
    f_index = fun (self: t_MyArray) (index: usize) -> self.[ index ]
  }
