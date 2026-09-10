module New_tests.Legacy__lean_core_models__lib.Phantom
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Foo (v_Self: Type0) = { __marker_trait_t_Foo:Prims.unit }

type t_Bar (v_F: Type0) {| i0: t_Foo v_F |} = { f_e_phantom:Core_models.Marker.t_PhantomData v_F }

let impl__new
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Foo v_F)
      (_: Prims.unit)
    : t_Bar v_F =
  { f_e_phantom = Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_F }
  <:
  t_Bar v_F
