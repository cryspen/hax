import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num

open Lean in
set_option hygiene false in
macro "declare_arith_ops" s:(&"signed" <|> &"unsigned") typeName:ident suffix:ident width:term : command => do
  let signed ← match s.raw[0].getKind with
  | `signed => pure true
  | `unsigned => pure false
  | _ => throw .unsupportedSyntax
  let ident (kind: String) := mkIdent (kind ++ "_" ++ suffix.getId.toString).toName

  let mut cmds ← Syntax.getArgs <$> `(
    namespace rust_primitives.arithmetic

    @[spec]
    def $(ident "wrapping_add") (x : $typeName) (y : $typeName) : RustM $typeName :=
      pure (x + y)

    @[spec]
    def $(ident "wrapping_sub") (x : $typeName) (y : $typeName) : RustM $typeName :=
      pure (x - y)

    @[spec]
    def $(ident "wrapping_mul") (x : $typeName) (y : $typeName) : RustM $typeName :=
      pure (x * y)
  )

  if signed then
    cmds := cmds.push $ ← `(
      def $(ident "pow") (x : $typeName) (y : u32) : RustM $typeName :=
        if x.toInt ^ y.toNat ≥ 2 ^ ($width - 1) || x.toInt ^ y.toNat < - 2 ^ ($width - 1)
        then .fail .integerOverflow
        else pure (x ^ y.toNat)
    )
  else
    cmds := cmds.push $ ← `(
      def $(ident "pow") (x : $typeName) (y : u32) : RustM $typeName :=
        if x.toNat ^ y.toNat ≥ 2 ^ $width
        then .fail .integerOverflow
        else pure (x ^ y.toNat)
    )

  cmds := cmds.push $ ← `(
    end rust_primitives.arithmetic
  )
  return ⟨mkNullNode cmds⟩

declare_arith_ops unsigned UInt8 u8 8
declare_arith_ops unsigned UInt16 u16 16
declare_arith_ops unsigned UInt32 u32 32
declare_arith_ops unsigned UInt64 u64 64
declare_arith_ops unsigned u128 u128 128
declare_arith_ops unsigned USize64 usize 64

declare_arith_ops signed Int8 i8 8
declare_arith_ops signed Int16 i16 16
declare_arith_ops signed Int32 i32 32
declare_arith_ops signed Int64 i64 64
declare_arith_ops signed i128 i128 128
declare_arith_ops signed ISize isize 64
