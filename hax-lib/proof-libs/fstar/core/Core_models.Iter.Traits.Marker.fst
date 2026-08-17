module Core_models.Iter.Traits.Marker
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::FusedIterator`]
class t_FusedIterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Iter.Traits.Iterator.t_Iterator
  v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_FusedIterator v_Self|} -> i._super_i0

/// See [`std::iter::TrustedLen`]
class t_TrustedLen (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Iter.Traits.Iterator.t_Iterator
  v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_TrustedLen v_Self|} -> i._super_i0
