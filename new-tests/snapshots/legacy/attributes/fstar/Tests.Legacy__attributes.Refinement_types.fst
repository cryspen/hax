module Tests.Legacy__attributes.Refinement_types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let t_BoundedU8 (v_MIN v_MAX: u8) = x: u8{x >=. v_MIN && x <=. v_MAX}

let bounded_u8 (x: t_BoundedU8 (mk_u8 12) (mk_u8 15)) (y: t_BoundedU8 (mk_u8 10) (mk_u8 11))
    : t_BoundedU8 (mk_u8 1) (mk_u8 23) = (x <: u8) +! (y <: u8) <: t_BoundedU8 (mk_u8 1) (mk_u8 23)

/// Even `u8` numbers. Constructing pub Even values triggers static
/// proofs in the extraction.
let t_Even = x: u8{(x %! mk_u8 2 <: u8) =. mk_u8 0}

let double (x: u8) : Prims.Pure t_Even (requires x <. mk_u8 127) (fun _ -> Prims.l_True) =
  x +! x <: t_Even

let double_refine (x: u8) : Prims.Pure t_Even (requires x <. mk_u8 127) (fun _ -> Prims.l_True) =
  x +! x <: t_Even

/// A string that contains no space.
let t_NoE =
  x:
  Alloc.String.t_String
    { let (_: Core_models.Str.Iter.t_Chars), (out: bool) =
        Core_models.Iter.Traits.Iterator.f_any #Core_models.Str.Iter.t_Chars
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Str.impl_str__chars (Core_models.Ops.Deref.f_deref #Alloc.String.t_String
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                string)
            <:
            Core_models.Str.Iter.t_Chars)
          (fun ch ->
              let ch:FStar.Char.char = ch in
              ch =. ' ' <: bool)
      in
      ~.out }

/// A modular mutliplicative inverse
let t_ModInverse (v_MOD: u32) =
  n:
  u32
    { (((cast (n <: u32) <: u128) *! (cast (v_MOD <: u32) <: u128) <: u128) %!
        (cast (v_MOD <: u32) <: u128)
        <:
        u128) =.
      mk_u128 1 }

/// A field element
let t_FieldElement = x: u16{x <=. mk_u16 2347}

/// Example of a specific constraint on a value
let t_CompressionFactor = x: u8{x =. mk_u8 4 || x =. mk_u8 5 || x =. mk_u8 10 || x =. mk_u8 11}

let t_BoundedAbsI16 (v_B: usize) =
  x:
  i16
    { (Rust_primitives.Hax.Int.from_machine v_B <: Hax_lib.Int.t_Int) < (32768 <: Hax_lib.Int.t_Int) &&
      (Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) >=
      (- (Rust_primitives.Hax.Int.from_machine v_B <: Hax_lib.Int.t_Int) <: Hax_lib.Int.t_Int) &&
      (Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) <=
      (Rust_primitives.Hax.Int.from_machine v_B <: Hax_lib.Int.t_Int) }

let impl (v_B: usize) : Core_models.Clone.t_Clone (t_BoundedAbsI16 v_B) =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': v_B: usize -> Core_models.Marker.t_Copy (t_BoundedAbsI16 v_B)

unfold
let impl_1 (v_B: usize) = impl_1' v_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_B: usize -> Core_models.Marker.t_StructuralPartialEq (t_BoundedAbsI16 v_B)

unfold
let impl_3 (v_B: usize) = impl_3' v_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_B: usize -> Core_models.Cmp.t_PartialEq (t_BoundedAbsI16 v_B) (t_BoundedAbsI16 v_B)

unfold
let impl_4 (v_B: usize) = impl_4' v_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_B: usize -> Core_models.Cmp.t_Eq (t_BoundedAbsI16 v_B)

unfold
let impl_2 (v_B: usize) = impl_2' v_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': v_B: usize -> Core_models.Cmp.t_PartialOrd (t_BoundedAbsI16 v_B) (t_BoundedAbsI16 v_B)

unfold
let impl_6 (v_B: usize) = impl_6' v_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': v_B: usize -> Core_models.Cmp.t_Ord (t_BoundedAbsI16 v_B)

unfold
let impl_5 (v_B: usize) = impl_5' v_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': v_B: usize -> Core_models.Hash.t_Hash (t_BoundedAbsI16 v_B)

unfold
let impl_7 (v_B: usize) = impl_7' v_B

let double_abs_i16 (v_N v_M: usize) (x: t_BoundedAbsI16 v_N)
    : Prims.Pure (t_BoundedAbsI16 v_M)
      (requires
        (Rust_primitives.Hax.Int.from_machine v_M <: Hax_lib.Int.t_Int) <
        (32768 <: Hax_lib.Int.t_Int) &&
        (Rust_primitives.Hax.Int.from_machine v_M <: Hax_lib.Int.t_Int) =
        ((Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int) * (2 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  Core_models.Ops.Arith.f_mul #(t_BoundedAbsI16 v_N)
    #i16
    #FStar.Tactics.Typeclasses.solve
    x
    (mk_i16 2)
  <:
  t_BoundedAbsI16 v_M
