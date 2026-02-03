import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num

open Lean in
set_option hygiene false in
macro "declare_arith_ops" s:(&"signed" <|> &"unsigned") typeName:ident suffix:ident width:term : command => do
  let ident (kind: String) := mkIdent (kind ++ "_" ++ suffix.getId.toString).toName
  `(
    namespace Rust_primitives.Arithmetic

    def $(ident "wrapping_add") (x : $typeName) (y : $typeName) : RustM $typeName :=
      pure (x + y)

    def $(ident "wrapping_sub") (x : $typeName) (y : $typeName) : RustM $typeName :=
      pure (x - y)

    def $(ident "wrapping_mul") (x : $typeName) (y : $typeName) : RustM $typeName :=
      pure (x * y)

    end Rust_primitives.Arithmetic
  )

declare_arith_ops signed UInt8 u8 8
declare_arith_ops signed UInt16 u16 16
declare_arith_ops signed UInt32 u32 32
declare_arith_ops signed UInt64 u64 64
declare_arith_ops signed u128 u128 128
declare_arith_ops signed USize64 usize 64

declare_arith_ops signed Int8 i8 8
declare_arith_ops signed Int16 i16 16
declare_arith_ops signed Int32 i32 32
declare_arith_ops signed Int64 i64 64
declare_arith_ops signed i128 i128 128
declare_arith_ops signed ISize isize 64
