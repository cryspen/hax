
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

class
  Tests.Legacy__traits.Implicit_dependencies_issue_667.Trait_definition.MyTrait
  (Self : Type)
  where
  my_method : Self -> Result Rust_primitives.Hax.Tuple0

structure
  Tests.Legacy__traits.Implicit_dependencies_issue_667.Define_type.MyType
  where


class Tests.Legacy__traits.Unconstrainted_types_issue_677.PolyOp
  (Self : Type)
  where
  op : u32 -> u32 -> Result u32

structure Tests.Legacy__traits.Unconstrainted_types_issue_677.Plus where


instance Tests.Legacy__traits.Unconstrainted_types_issue_677.Impl :
  Tests.Legacy__traits.Unconstrainted_types_issue_677.PolyOp
  Tests.Legacy__traits.Unconstrainted_types_issue_677.Plus
  where
  op (x : u32) (y : u32) := do (← x +? y)

structure Tests.Legacy__traits.Unconstrainted_types_issue_677.Times where


instance Tests.Legacy__traits.Unconstrainted_types_issue_677.Impl_1 :
  Tests.Legacy__traits.Unconstrainted_types_issue_677.PolyOp
  Tests.Legacy__traits.Unconstrainted_types_issue_677.Times
  where
  op (x : u32) (y : u32) := do (← x *? y)

def Tests.Legacy__traits.Unconstrainted_types_issue_677.twice
  (OP : Type)
  [(Tests.Legacy__traits.Unconstrainted_types_issue_677.PolyOp OP)]
  (x : u32)
  : Result u32
  := do
  (← Tests.Legacy__traits.Unconstrainted_types_issue_677.PolyOp.op x x)

def Tests.Legacy__traits.Unconstrainted_types_issue_677.both
  (x : u32)
  : Result (Rust_primitives.Hax.Tuple2 u32 u32)
  := do
  (Rust_primitives.Hax.Tuple2.mk
    (← Tests.Legacy__traits.Unconstrainted_types_issue_677.twice
        Tests.Legacy__traits.Unconstrainted_types_issue_677.Plus x)
    (← Tests.Legacy__traits.Unconstrainted_types_issue_677.twice
        Tests.Legacy__traits.Unconstrainted_types_issue_677.Times x))

structure
  Tests.Legacy__traits.Type_alias_bounds_issue_707.StructWithGenericBounds
  (T : Type) [(Core.Clone.Clone T)] where
  _0 : T

abbrev Tests.Legacy__traits.Type_alias_bounds_issue_707.SynonymA :=
(Tests.Legacy__traits.Type_alias_bounds_issue_707.StructWithGenericBounds T)

abbrev Tests.Legacy__traits.Type_alias_bounds_issue_707.SynonymB :=
(Tests.Legacy__traits.Type_alias_bounds_issue_707.StructWithGenericBounds
  (Rust_primitives.Hax.Tuple2 T T))

class Tests.Legacy__traits.Recursive_trait_with_assoc_type.Trait1
  (Self : Type)
  where
  T : Type
  [_constr_10693293807949125845 :
    (Tests.Legacy__traits.Recursive_trait_with_assoc_type.Trait1 T)]

class Tests.Legacy__traits.Recursive_trait_with_assoc_type.Trait2
  (Self : Type)
  where
  [_constr_16929467391406391938 :
  (Tests.Legacy__traits.Recursive_trait_with_assoc_type.Trait1 Self)]
  U : Type

structure Tests.Legacy__traits.Interlaced_consts_types.Bar
  -- Unsupported const param (FooType : Type) where
  _0 : (RustArray FooType FooConst)

class Tests.Legacy__traits.Interlaced_consts_types.Foo
  (Self : Type) -- Unsupported const param (FooType : Type)
  where
  fun -- Unsupported const param (FunType : Type) :
    (RustArray FooType FooConst)
    -> (RustArray FunType FunConst)
    -> Result Rust_primitives.Hax.Tuple0

instance Tests.Legacy__traits.Interlaced_consts_types.Impl
  -- Unsupported const param (FooType : Type) (SelfType : Type) :
  Tests.Legacy__traits.Interlaced_consts_types.Foo SelfType FooConst FooType
  where
  fun -- Unsupported const param (FunType : Type) (x :
    (RustArray FooType FooConst))
    (y : (RustArray FunType FunConst))
    := do
    Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__traits.Implicit_explicit_calling_conventions.Type
  (TypeArg : Type) -- Unsupported const param where
  field : (RustArray TypeArg ConstArg)

class Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait
  (Self : Type) (TypeArg : Type) -- Unsupported const param
  where
  method (MethodTypeArg : Type) -- Unsupported const param :
    Self
    -> TypeArg
    -> (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Type
      TypeArg
      ConstArg)
    -> Result Rust_primitives.Hax.Tuple0
  associated_function (MethodTypeArg : Type) -- Unsupported const param :
    Self
    -> TypeArg
    -> (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Type
      TypeArg
      ConstArg)
    -> Result Rust_primitives.Hax.Tuple0

instance Tests.Legacy__traits.Implicit_explicit_calling_conventions.Impl
  (TypeArg : Type) -- Unsupported const param :
  Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait
  Rust_primitives.Hax.Tuple0
  TypeArg
  ConstArg
  where
  method (MethodTypeArg : Type) -- Unsupported const param (self :
    Rust_primitives.Hax.Tuple0)
    (value_TypeArg : TypeArg)
    (value_Type :
    (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Type
      TypeArg
      ConstArg))
    := do
    Rust_primitives.Hax.Tuple0.mk
  associated_function (MethodTypeArg : Type) -- Unsupported const param (_self :
    Rust_primitives.Hax.Tuple0)
    (value_TypeArg : TypeArg)
    (value_Type :
    (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Type
      TypeArg
      ConstArg))
    := do
    Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__traits.Implicit_explicit_calling_conventions.method_caller
  (MethodTypeArg : Type)
  (TypeArg : Type)
  -- Unsupported const param
  -- Unsupported const param
  (ImplTrait : Type)
  [(Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait
    ImplTrait
    TypeArg
    ConstArg)]
  (x : ImplTrait)
  (value_TypeArg : TypeArg)
  (value_Type :
  (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Type
    TypeArg
    ConstArg))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait.method
        MethodTypeArg
        MethodConstArg x value_TypeArg value_Type));
  Rust_primitives.Hax.Tuple0.mk

def
  Tests.Legacy__traits.Implicit_explicit_calling_conventions.associated_function_caller
  (MethodTypeArg : Type)
  (TypeArg : Type)
  -- Unsupported const param
  -- Unsupported const param
  (ImplTrait : Type)
  [(Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait
    ImplTrait
    TypeArg
    ConstArg)]
  (x : ImplTrait)
  (value_TypeArg : TypeArg)
  (value_Type :
  (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Type
    TypeArg
    ConstArg))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait.associated_function
        MethodTypeArg
        MethodConstArg x value_TypeArg value_Type));
  Rust_primitives.Hax.Tuple0.mk

class Tests.Legacy__traits.Implicit_explicit_calling_conventions.SubTrait
  (Self : Type) (TypeArg : Type) -- Unsupported const param
  where
  [_constr_13222719583123837337 :
  (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait
    Self
    TypeArg
    ConstArg)]
  AssocType : Type
  [_constr_6861958164448569051 :
    (Tests.Legacy__traits.Implicit_explicit_calling_conventions.Trait
      AssocType
      TypeArg
      ConstArg)]

instance Tests.Legacy__traits.Implicit_dependencies_issue_667.Impl_type.Impl :
  Tests.Legacy__traits.Implicit_dependencies_issue_667.Trait_definition.MyTrait
  Tests.Legacy__traits.Implicit_dependencies_issue_667.Define_type.MyType
  where
  my_method (self :
    Tests.Legacy__traits.Implicit_dependencies_issue_667.Define_type.MyType)
    := do
    Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped where
  _0 : i32

instance Tests.Legacy__traits.Implement_arithmetic_trait.Impl :
  Core.Ops.Arith.Add
  Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped
  Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped
  where
  Output := Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped
  add (self : Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped)
    (rhs : Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped)
    := do
    (Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped.mk
      (← (Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped._0 self)
        +? (Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped._0 rhs)))

def Tests.Legacy__traits.Implement_arithmetic_trait.test
  (x : Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped)
  (y : Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped)
  : Result Tests.Legacy__traits.Implement_arithmetic_trait.Wrapped
  := do
  (← Core.Ops.Arith.Add.add x y)

class Tests.Legacy__traits.Impl_expr_in_goal.T1 (Self : Type) where
  Assoc : Type

class Tests.Legacy__traits.Impl_expr_in_goal.T2 (Self : Type) where


instance Tests.Legacy__traits.Impl_expr_in_goal.Impl
  (U : Type)
  [(Tests.Legacy__traits.Impl_expr_in_goal.T1 U)]
  [(Tests.Legacy__traits.Impl_expr_in_goal.T2 TODO_LINE_701)]
  :
  Tests.Legacy__traits.Impl_expr_in_goal.T2 U
  where


class Tests.Legacy__traits.For_clauses.Issue_495.Minimized_3.Trait
  (Self : Type)
  where


instance Tests.Legacy__traits.For_clauses.Issue_495.Minimized_3.Impl
  (P : Type)
  [-- unsupported constraint]
  [(Core.Ops.Function.FnMut P (Rust_primitives.Hax.Tuple1 u8))]
  :
  Tests.Legacy__traits.For_clauses.Issue_495.Minimized_3.Trait P
  where


class Tests.Legacy__traits.For_clauses.Foo (Self : Type) (T : Type) where
  to_t : Self -> Result T

def Tests.Legacy__traits.For_clauses._f
  (X : Type) [(Tests.Legacy__traits.For_clauses.Foo X u8)] (x : X)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Tests.Legacy__traits.For_clauses.Foo.to_t x));
  Rust_primitives.Hax.Tuple0.mk

class Tests.Legacy__traits.Default_traits_parameters.Bar
  (Self : Type) (T : Type)
  where


class Tests.Legacy__traits.Default_traits_parameters.Foo (Self : Type) where
  [_constr_11141233769666008475 :
  (Tests.Legacy__traits.Default_traits_parameters.Bar Self U)]
  U : Type

class Tests.Legacy__traits.Block_size.BlockSizeUser (Self : Type) where
  BlockSize : Type

class Tests.Legacy__traits.Block_size.ParBlocksSizeUser (Self : Type) where
  [_constr_1032993800281319343 :
  (Tests.Legacy__traits.Block_size.BlockSizeUser Self)]


class Tests.Legacy__traits.Block_size.BlockBackend (Self : Type) where
  [_constr_12752098123861594988 :
  (Tests.Legacy__traits.Block_size.ParBlocksSizeUser Self)]
  proc_block :
    (Alloc.Vec.Vec TODO_LINE_701 Alloc.Alloc.Global)
    -> Result Rust_primitives.Hax.Tuple0

class Tests.Legacy__traits.SuperTrait (Self : Type) where
  [_constr_14156401398203956914 : (Core.Clone.Clone Self)]
  function_of_super_trait : Self -> Result u32

instance Tests.Legacy__traits.Impl : Tests.Legacy__traits.SuperTrait i32 where
  function_of_super_trait (self : i32) := do
    (← Rust_primitives.Hax.cast_op (← Core.Num.Impl_2.abs self))

structure Tests.Legacy__traits.Struct where


class Tests.Legacy__traits.Bar (Self : Type) where
  bar : Self -> Result Rust_primitives.Hax.Tuple0

def Tests.Legacy__traits.Impl_2.method
  (T : Type) [(Tests.Legacy__traits.Bar T)] (x : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__traits.Bar.bar x)

def Tests.Legacy__traits.closure_impl_expr
  (I : Type)
  [(Core.Iter.Traits.Iterator.Iterator I)]
  [-- unsupported constraint]
  (it : I)
  : Result (Alloc.Vec.Vec Rust_primitives.Hax.Tuple0 Alloc.Alloc.Global)
  := do
  (← Core.Iter.Traits.Iterator.Iterator.collect
      (Alloc.Vec.Vec Rust_primitives.Hax.Tuple0 Alloc.Alloc.Global)
      (← Core.Iter.Traits.Iterator.Iterator.map
          Rust_primitives.Hax.Tuple0
          Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
          it
          (fun x => (do x : Result Rust_primitives.Hax.Tuple0))))

def Tests.Legacy__traits.closure_impl_expr_fngen
  (I : Type)
  (F : Type)
  [(Core.Iter.Traits.Iterator.Iterator I)]
  [-- unsupported constraint]
  [(Core.Ops.Function.FnMut
    F
    (Rust_primitives.Hax.Tuple1 Rust_primitives.Hax.Tuple0))]
  [-- unsupported constraint]
  (it : I)
  (f : F)
  : Result (Alloc.Vec.Vec Rust_primitives.Hax.Tuple0 Alloc.Alloc.Global)
  := do
  (← Core.Iter.Traits.Iterator.Iterator.collect
      (Alloc.Vec.Vec Rust_primitives.Hax.Tuple0 Alloc.Alloc.Global)
      (← Core.Iter.Traits.Iterator.Iterator.map Rust_primitives.Hax.Tuple0 F
          it
          f))

inductive Tests.Legacy__traits.Error : Type
| Fail : Tests.Legacy__traits.Error 


def Tests.Legacy__traits.Error
  (x : Tests.Legacy__traits.Error)
  : Result isize
  := do
  (match x with | (Tests.Legacy__traits.Error.Fail ) => do (0 : isize))

def Tests.Legacy__traits.Impl_3.for_application_callback
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0 -> Result Tests.Legacy__traits.Error
  := do
  (fun _ => (do
      Tests.Legacy__traits.Error.Fail : Result Tests.Legacy__traits.Error))

def Tests.Legacy__traits.iter_option
  (T : Type) (x : (Core.Option.Option T))
  : Result (Core.Option.IntoIter T)
  := do
  (← Core.Iter.Traits.Collect.IntoIterator.into_iter
      (← Core.Option.Impl.as_ref T x))

def Tests.Legacy__traits.use_impl_trait
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let iter : (Core.Option.IntoIter Bool) ← (pure
    (← Tests.Legacy__traits.iter_option Bool (Core.Option.Option.Some false)));
  let ⟨tmp0, out⟩ ← (pure (← Core.Iter.Traits.Iterator.Iterator.next iter));
  let iter : (Core.Option.IntoIter Bool) ← (pure tmp0);
  let _ ← (pure out);
  Rust_primitives.Hax.Tuple0.mk

class Tests.Legacy__traits.Foo (Self : Type) where
  AssocType : Type
  [_constr_13701427516003292911 : (Tests.Legacy__traits.SuperTrait AssocType)]
  N : usize
  assoc_f : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
  method_f : Self -> Result Rust_primitives.Hax.Tuple0
  assoc_type [(Core.Marker.Copy AssocType)] :
    AssocType -> Result Rust_primitives.Hax.Tuple0

class Tests.Legacy__traits.Lang (Self : Type) where
  Var : Type
  s : Self -> i32 -> Result (Rust_primitives.Hax.Tuple2 Self Var)

def Tests.Legacy__traits.f
  (T : Type) [(Tests.Legacy__traits.Foo T)] (x : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__traits.Foo.assoc_f Rust_primitives.Hax.Tuple0.mk));
  (← Tests.Legacy__traits.Foo.method_f x)

def Tests.Legacy__traits.g
  (T : Type) [(Tests.Legacy__traits.Foo T)] (x : TODO_LINE_701)
  : Result u32
  := do
  (← Tests.Legacy__traits.SuperTrait.function_of_super_trait x)

instance Tests.Legacy__traits.Impl_1 :
  Tests.Legacy__traits.Foo Rust_primitives.Hax.Tuple0
  where
  AssocType := i32
  N := do (32 : usize)
  assoc_f (_ : Rust_primitives.Hax.Tuple0) := do Rust_primitives.Hax.Tuple0.mk
  method_f (self : Rust_primitives.Hax.Tuple0) := do
    (← Tests.Legacy__traits.Foo.assoc_f Rust_primitives.Hax.Tuple0.mk)
  assoc_type (_ : i32) := do Rust_primitives.Hax.Tuple0.mk

abbrev Tests.Legacy__traits.Typenum_perf.I20 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt
                            (Typenum.Uint.UInt
                              (Typenum.Uint.UInt
                                (Typenum.Uint.UInt
                                  (Typenum.Uint.UInt
                                    (Typenum.Uint.UInt
                                      (Typenum.Uint.UInt
                                        Typenum.Uint.UTerm
                                        Typenum.Bit.B1)
                                      Typenum.Bit.B1)
                                    Typenum.Bit.B1)
                                  Typenum.Bit.B1)
                                Typenum.Bit.B1)
                              Typenum.Bit.B1)
                            Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I19 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt
                            (Typenum.Uint.UInt
                              (Typenum.Uint.UInt
                                (Typenum.Uint.UInt
                                  (Typenum.Uint.UInt
                                    (Typenum.Uint.UInt
                                      Typenum.Uint.UTerm
                                      Typenum.Bit.B1)
                                    Typenum.Bit.B1)
                                  Typenum.Bit.B1)
                                Typenum.Bit.B1)
                              Typenum.Bit.B1)
                            Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I18 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt
                            (Typenum.Uint.UInt
                              (Typenum.Uint.UInt
                                (Typenum.Uint.UInt
                                  (Typenum.Uint.UInt
                                    Typenum.Uint.UTerm
                                    Typenum.Bit.B1)
                                  Typenum.Bit.B1)
                                Typenum.Bit.B1)
                              Typenum.Bit.B1)
                            Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I17 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt
                            (Typenum.Uint.UInt
                              (Typenum.Uint.UInt
                                (Typenum.Uint.UInt
                                  Typenum.Uint.UTerm
                                  Typenum.Bit.B1)
                                Typenum.Bit.B1)
                              Typenum.Bit.B1)
                            Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I16 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt
                            (Typenum.Uint.UInt
                              (Typenum.Uint.UInt
                                Typenum.Uint.UTerm
                                Typenum.Bit.B1)
                              Typenum.Bit.B1)
                            Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I15 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt
                            (Typenum.Uint.UInt
                              Typenum.Uint.UTerm
                              Typenum.Bit.B1)
                            Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I14 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I13 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I12 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I11 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I10 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I9 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I8 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I7 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I6 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I5 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I4 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
      Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I3 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt
    (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
    Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I2 := (Typenum.Uint.UInt
  (Typenum.Uint.UInt Typenum.Uint.UTerm Typenum.Bit.B1)
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I1 := (Typenum.Uint.UInt
  Typenum.Uint.UTerm
  Typenum.Bit.B1)

abbrev Tests.Legacy__traits.Typenum_perf.I0 := Typenum.Uint.UTerm

def Tests.Legacy__traits.Typenum_perf._f
  (T : Type)
  [(Typenum.Type_operators.IsLess
    T
    (Typenum.Uint.UInt
      (Typenum.Uint.UInt
        (Typenum.Uint.UInt
          (Typenum.Uint.UInt
            (Typenum.Uint.UInt
              (Typenum.Uint.UInt
                (Typenum.Uint.UInt
                  (Typenum.Uint.UInt
                    (Typenum.Uint.UInt
                      (Typenum.Uint.UInt
                        (Typenum.Uint.UInt
                          (Typenum.Uint.UInt
                            (Typenum.Uint.UInt
                              (Typenum.Uint.UInt
                                (Typenum.Uint.UInt
                                  (Typenum.Uint.UInt
                                    (Typenum.Uint.UInt
                                      (Typenum.Uint.UInt
                                        (Typenum.Uint.UInt
                                          (Typenum.Uint.UInt
                                            Typenum.Uint.UTerm
                                            Typenum.Bit.B1)
                                          Typenum.Bit.B1)
                                        Typenum.Bit.B1)
                                      Typenum.Bit.B1)
                                    Typenum.Bit.B1)
                                  Typenum.Bit.B1)
                                Typenum.Bit.B1)
                              Typenum.Bit.B1)
                            Typenum.Bit.B1)
                          Typenum.Bit.B1)
                        Typenum.Bit.B1)
                      Typenum.Bit.B1)
                    Typenum.Bit.B1)
                  Typenum.Bit.B1)
                Typenum.Bit.B1)
              Typenum.Bit.B1)
            Typenum.Bit.B1)
          Typenum.Bit.B1)
        Typenum.Bit.B1)
      Typenum.Bit.B1))]
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__traits.Implicit_dependencies_issue_667.Use_type.some_function
  (x : Tests.Legacy__traits.Implicit_dependencies_issue_667.Define_type.MyType)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__traits.Implicit_dependencies_issue_667.Trait_definition.MyTrait.my_method
      x)

def Tests.Legacy__traits.For_clauses.Issue_495.original_function_from_495
  (list : (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _indices ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.collect
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
        (← Core.Iter.Traits.Iterator.Iterator.filter u8 -> Result Bool
            (Core.Ops.Range.Range.mk (start := (0 : u8)) (_end := (5 : u8)))
            (fun i => (do
                let ⟨_, out⟩ ← (pure
                  (← Core.Iter.Traits.Iterator.Iterator.any u8 -> Result Bool
                      (← Core.Slice.Impl.iter u8
                          (← Core.Ops.Deref.Deref.deref list))
                      (fun n => (do
                          (← Core.Cmp.PartialEq.eq n i) : Result Bool))));
                out : Result Bool)))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__traits.For_clauses.Issue_495.minimized_1
  (list : (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  (← Core.Iter.Traits.Iterator.Iterator.collect
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
      (← Core.Iter.Traits.Iterator.Iterator.filter u8 -> Result Bool
          (Core.Ops.Range.Range.mk (start := (0 : u8)) (_end := (5 : u8)))
          (fun _ => (do true : Result Bool))))

def Tests.Legacy__traits.For_clauses.Issue_495.minimized_2
  (it :
  (Core.Iter.Adapters.Filter.Filter
    (Core.Ops.Range.Range u8)
    u8 -> Result Bool))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _indices ← (pure
    (← Core.Iter.Traits.Iterator.Iterator.collect
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) it));
  Rust_primitives.Hax.Tuple0.mk