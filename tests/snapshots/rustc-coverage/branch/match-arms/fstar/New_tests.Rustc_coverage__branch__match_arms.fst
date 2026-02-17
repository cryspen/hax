module New_tests.Rustc_coverage__branch__match_arms
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Enum =
  | Enum_A : u32 -> t_Enum
  | Enum_B : u32 -> t_Enum
  | Enum_C : u32 -> t_Enum
  | Enum_D : u32 -> t_Enum

let impl: Core_models.Clone.t_Clone t_Enum =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Marker.t_Copy t_Enum

unfold
let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Fmt.t_Debug t_Enum

unfold
let impl_2 = impl_2'

let consume (#v_T: Type0) (x: v_T) : Prims.unit =
  let _:v_T = Core_models.Hint.black_box #v_T x in
  ()

/// @fail(extraction): proverif(HAX0008)
let match_arms (value: t_Enum) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 1)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          ())
  in
  let _:Prims.unit =
    match value <: t_Enum with
    | Enum_D d -> consume #u32 d
    | Enum_C c -> consume #u32 c
    | Enum_B b -> consume #u32 b
    | Enum_A a -> consume #u32 a
  in
  let _:Prims.unit = consume #i32 (mk_i32 0) in
  ()

/// @fail(extraction): proverif(HAX0008)
let or_patterns (value: t_Enum) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 1)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          ())
  in
  let _:Prims.unit =
    match value <: t_Enum with
    | Enum_D x | Enum_C x -> consume #u32 x
    | Enum_B y | Enum_A y -> consume #u32 y
  in
  let _:Prims.unit = consume #i32 (mk_i32 0) in
  ()

/// @fail(extraction): proverif(HAX0008, HAX0008)
let guards (value: t_Enum) (cond: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 1)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          ())
  in
  let _:Prims.unit =
    match
      (match value <: t_Enum with
        | Enum_D d ->
          (match cond <: bool with
            | true ->
              Core_models.Option.Option_Some (consume #u32 d)
              <:
              Core_models.Option.t_Option Prims.unit
            | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
        | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
      <:
      Core_models.Option.t_Option Prims.unit
    with
    | Core_models.Option.Option_Some x -> x
    | Core_models.Option.Option_None  ->
      match
        (match value <: t_Enum with
          | Enum_C c ->
            (match cond <: bool with
              | true ->
                Core_models.Option.Option_Some (consume #u32 c)
                <:
                Core_models.Option.t_Option Prims.unit
              | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
          | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
        <:
        Core_models.Option.t_Option Prims.unit
      with
      | Core_models.Option.Option_Some x -> x
      | Core_models.Option.Option_None  ->
        match
          (match value <: t_Enum with
            | Enum_B b ->
              (match cond <: bool with
                | true ->
                  Core_models.Option.Option_Some (consume #u32 b)
                  <:
                  Core_models.Option.t_Option Prims.unit
                | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
            | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
          <:
          Core_models.Option.t_Option Prims.unit
        with
        | Core_models.Option.Option_Some x -> x
        | Core_models.Option.Option_None  ->
          match
            (match value <: t_Enum with
              | Enum_A a ->
                (match cond <: bool with
                  | true ->
                    Core_models.Option.Option_Some (consume #u32 a)
                    <:
                    Core_models.Option.t_Option Prims.unit
                  | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
              | _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option Prims.unit)
            <:
            Core_models.Option.t_Option Prims.unit
          with
          | Core_models.Option.Option_Some x -> x
          | Core_models.Option.Option_None  -> consume #i32 (mk_i32 0)
  in
  let _:Prims.unit = consume #i32 (mk_i32 0) in
  ()

/// @fail(extraction): proverif(HAX0008)
let main__call_everything (e: t_Enum) : (Prims.unit & Prims.unit) =
  let _:Prims.unit = match_arms e in
  let _:Prims.unit = or_patterns e in
  Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Array
            bool (mk_usize 3))
        #FStar.Tactics.Typeclasses.solve
        (let list = [false; false; true] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
          Rust_primitives.Hax.array_of_list 3 list)
      <:
      Core_models.Array.Iter.t_IntoIter bool (mk_usize 3))
    ()
    (fun temp_0_ cond ->
        let _:Prims.unit = temp_0_ in
        let cond:bool = cond in
        guards e cond <: Prims.unit),
  ()
  <:
  (Prims.unit & Prims.unit)

/// @fail(extraction): proverif(HAX0008)
/// @fail(extraction): proverif(HAX0008, HAX0008)
let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let _:Prims.unit = main__call_everything (Enum_A (mk_u32 0) <: t_Enum) in
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_u32 0)
      (mk_u32 2)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      ()
      (fun temp_0_ b ->
          let _:Prims.unit = temp_0_ in
          let b:u32 = b in
          main__call_everything (Enum_B b <: t_Enum) <: Prims.unit)
  in
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_u32 0)
      (mk_u32 4)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      ()
      (fun temp_0_ c ->
          let _:Prims.unit = temp_0_ in
          let c:u32 = c in
          main__call_everything (Enum_C c <: t_Enum) <: Prims.unit)
  in
  Rust_primitives.Hax.Folds.fold_range (mk_u32 0)
    (mk_u32 8)
    (fun temp_0_ temp_1_ ->
        let _:Prims.unit = temp_0_ in
        let _:u32 = temp_1_ in
        true)
    ()
    (fun temp_0_ d ->
        let _:Prims.unit = temp_0_ in
        let d:u32 = d in
        main__call_everything (Enum_D d <: t_Enum) <: Prims.unit),
  ()
  <:
  (Prims.unit & Prims.unit)
