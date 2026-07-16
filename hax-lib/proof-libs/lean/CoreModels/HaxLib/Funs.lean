import Aeneas
import CoreModels.Command
import CoreModels.Core.TypesPrologue
import CoreModels.Core.Types
open Aeneas
open Aeneas.Std hiding namespace core
open Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace CoreModels

namespace core

/-- [hax_lib::int::{core::cmp::PartialOrd<hax_lib::int::Int> for hax_lib::int::Int}::le]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 77:46-77:56
    Name pattern: [hax_lib::int::{core::cmp::PartialOrd<hax_lib::int::Int, hax_lib::int::Int>}::le]
    Visibility: public -/
@[rust_fun
  "hax_lib::int::{core::cmp::PartialOrd<hax_lib::int::Int, hax_lib::int::Int>}::le"]
def hax_lib.int.Int.Insts.CoreCmpPartialOrdInt.le
  : hax_lib.int.Int → hax_lib.int.Int → Result Bool :=
  fun a b => ok (decide (a ≤ b))

/-- [hax_lib::int::{core::ops::arith::Add<hax_lib::int::Int, hax_lib::int::Int> for hax_lib::int::Int}::add]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 92:8-92:49
    Name pattern: [hax_lib::int::{core::ops::arith::Add<hax_lib::int::Int, hax_lib::int::Int, hax_lib::int::Int>}::add]
    Visibility: public -/
@[rust_fun
  "hax_lib::int::{core::ops::arith::Add<hax_lib::int::Int, hax_lib::int::Int, hax_lib::int::Int>}::add"]
def hax_lib.int.Int.Insts.CoreOpsArithAddIntInt.add
  : hax_lib.int.Int → hax_lib.int.Int → Result hax_lib.int.Int := fun a b => ok (a + b)

/-- [hax_lib::int::{core::ops::arith::Sub<hax_lib::int::Int, hax_lib::int::Int> for hax_lib::int::Int}::sub]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 100:8-100:49
    Name pattern: [hax_lib::int::{core::ops::arith::Sub<hax_lib::int::Int, hax_lib::int::Int, hax_lib::int::Int>}::sub]
    Visibility: public -/
@[rust_fun
  "hax_lib::int::{core::ops::arith::Sub<hax_lib::int::Int, hax_lib::int::Int, hax_lib::int::Int>}::sub"]
def hax_lib.int.Int.Insts.CoreOpsArithSubIntInt.sub
  : hax_lib.int.Int → hax_lib.int.Int → Result hax_lib.int.Int := fun a b => ok (a - b)

/-- [hax_lib::int::{core::ops::arith::Mul<hax_lib::int::Int, hax_lib::int::Int> for hax_lib::int::Int}::mul]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 108:8-108:49
    Name pattern: [hax_lib::int::{core::ops::arith::Mul<hax_lib::int::Int, hax_lib::int::Int, hax_lib::int::Int>}::mul]
    Visibility: public -/
@[rust_fun
  "hax_lib::int::{core::ops::arith::Mul<hax_lib::int::Int, hax_lib::int::Int, hax_lib::int::Int>}::mul"]
def hax_lib.int.Int.Insts.CoreOpsArithMulIntInt.mul
  : hax_lib.int.Int → hax_lib.int.Int → Result hax_lib.int.Int := fun a b => ok (a * b)

/-- [hax_lib::int::{hax_lib::int::ToInt for u8}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<u8>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<u8>}::to_int"]
def hax_lib.U8.Insts.Hax_libIntToInt.to_int : Std.U8 → Result hax_lib.int.Int :=
  fun x => ok (x.val : Int)

/-- [hax_lib::int::{hax_lib::int::ToInt for u16}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<u16>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<u16>}::to_int"]
def hax_lib.U16.Insts.Hax_libIntToInt.to_int : Std.U16 → Result hax_lib.int.Int :=
  fun x => ok (x.val : Int)

/-- [hax_lib::int::{hax_lib::int::ToInt for u32}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<u32>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<u32>}::to_int"]
def hax_lib.U32.Insts.Hax_libIntToInt.to_int : Std.U32 → Result hax_lib.int.Int :=
  fun x => ok (x.val : Int)

/-- [hax_lib::int::{hax_lib::int::ToInt for u64}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<u64>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<u64>}::to_int"]
def hax_lib.U64.Insts.Hax_libIntToInt.to_int : Std.U64 → Result hax_lib.int.Int :=
  fun x => ok (x.val : Int)

/-- [hax_lib::int::{hax_lib::int::ToInt for u128}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<u128>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<u128>}::to_int"]
def hax_lib.U128.Insts.Hax_libIntToInt.to_int : Std.U128 → Result hax_lib.int.Int :=
  fun x => ok (x.val : Int)

/-- [hax_lib::int::{hax_lib::int::ToInt for usize}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<usize>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<usize>}::to_int"]
def hax_lib.Usize.Insts.Hax_libIntToInt.to_int : Std.Usize → Result hax_lib.int.Int :=
  fun x => ok (x.val : Int)

/-- [hax_lib::int::{hax_lib::int::ToInt for i8}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<i8>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<i8>}::to_int"]
def hax_lib.I8.Insts.Hax_libIntToInt.to_int : Std.I8 → Result hax_lib.int.Int :=
  fun x => ok x.val

/-- [hax_lib::int::{hax_lib::int::ToInt for i16}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<i16>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<i16>}::to_int"]
def hax_lib.I16.Insts.Hax_libIntToInt.to_int : Std.I16 → Result hax_lib.int.Int :=
  fun x => ok x.val

/-- [hax_lib::int::{hax_lib::int::ToInt for i32}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<i32>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<i32>}::to_int"]
def hax_lib.I32.Insts.Hax_libIntToInt.to_int : Std.I32 → Result hax_lib.int.Int :=
  fun x => ok x.val

/-- [hax_lib::int::{hax_lib::int::ToInt for i64}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<i64>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<i64>}::to_int"]
def hax_lib.I64.Insts.Hax_libIntToInt.to_int : Std.I64 → Result hax_lib.int.Int :=
  fun x => ok x.val

/-- [hax_lib::int::{hax_lib::int::ToInt for i128}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<i128>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<i128>}::to_int"]
def hax_lib.I128.Insts.Hax_libIntToInt.to_int : Std.I128 → Result hax_lib.int.Int :=
  fun x => ok x.val

/-- [hax_lib::int::{hax_lib::int::ToInt for isize}::to_int]:
    Source: '/cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/src/dummy.rs', lines 155:16-155:38
    Name pattern: [hax_lib::int::{hax_lib::int::ToInt<isize>}::to_int]
    Visibility: public -/
@[rust_fun "hax_lib::int::{hax_lib::int::ToInt<isize>}::to_int"]
def hax_lib.Isize.Insts.Hax_libIntToInt.to_int : Std.Isize → Result hax_lib.int.Int :=
  fun x => ok x.val

end core

end CoreModels
