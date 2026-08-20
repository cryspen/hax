import CoreModels.Core.Funs
import CoreModels.MissingAeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result ScalarElab

set_option mvcgen.warning false

/-! # Specs for `rust_primitives::arithmetic` -/

/-! ## `pow` -/

theorem upow_partialSpec {ty : UScalarTy} (x : UScalar ty) (n : Std.U32) :
    partialSpec (UScalar.tryMk ty (x.val ^ n.val))
      (fun r => r.val = x.val ^ n.val ∧ x.val ^ n.val ≤ 2 ^ ty.numBits - 1)
      (fun | .integerOverflow => x.val ^ n.val > 2 ^ ty.numBits - 1 | _ => False)
      False := by
  grind [UScalar.tryMk, Result.ofOption, UScalar.tryMkOpt_eq]

theorem ipow_partialSpec {ty : IScalarTy} (x : IScalar ty) (n : Std.U32) :
    partialSpec (IScalar.tryMk ty (x.val ^ n.val))
      (fun r => r.val = x.val ^ n.val ∧ -2 ^ (ty.numBits - 1) ≤ x.val ^ n.val ∧ x.val ^ n.val ≤ 2 ^ (ty.numBits - 1) - 1)
      (fun | .integerOverflow => x.val ^ n.val < -2 ^ (ty.numBits - 1) ∨ x.val ^ n.val > 2 ^ (ty.numBits - 1) - 1 | _ => False)
      False := by
  grind [IScalar.tryMk, Result.ofOption, IScalar.tryMkOpt_eq]

/-! `'S` spells the model name up to case (`pow_'S ~> pow_U8`) and `%ToLowerCase`
lowercases it to the Rust spelling (`pow_u8`). -/

uscalar @[step] theorem rust_primitives.arithmetic.«%S».pow_spec (x : «%S») (n : Std.U32) :
    partialSpec ((%ToLowerCase rust_primitives.arithmetic.«pow_'S») x n)
      (fun r => r.val = x.val ^ n.val ∧ x.val ^ n.val ≤ «%S».max)
      (fun | .integerOverflow => x.val ^ n.val > «%S».max | _ => False)
      False := by
  simp only [«%S».max_def, «%S».numBits_def]
  exact upow_partialSpec x n

iscalar @[step] theorem rust_primitives.arithmetic.«%S».pow_spec (x : «%S») (n : Std.U32) :
    partialSpec ((%ToLowerCase rust_primitives.arithmetic.«pow_'S») x n)
      (fun r => r.val = x.val ^ n.val ∧
                «%S».min ≤ x.val ^ n.val ∧ x.val ^ n.val ≤ «%S».max)
      (fun | .integerOverflow => x.val ^ n.val < «%S».min ∨ x.val ^ n.val > «%S».max
           | _ => False)
      False := by
  simp only [«%S».max_def, «%S».min_def, «%S».numBits_def]
  exact ipow_partialSpec x n

end CoreModels
