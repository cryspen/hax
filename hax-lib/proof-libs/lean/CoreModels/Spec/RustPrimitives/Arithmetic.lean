import CoreModels.Core.Funs

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

attribute [spec]
  rust_primitives.arithmetic.from_le_bytes_u8
  rust_primitives.arithmetic.from_le_bytes_u16
  rust_primitives.arithmetic.from_le_bytes_u32
  rust_primitives.arithmetic.from_le_bytes_u64
  rust_primitives.arithmetic.from_le_bytes_u128
  rust_primitives.arithmetic.from_le_bytes_usize
  rust_primitives.arithmetic.to_le_bytes_u8
  rust_primitives.arithmetic.to_le_bytes_u16
  rust_primitives.arithmetic.to_le_bytes_u32
  rust_primitives.arithmetic.to_le_bytes_u64
  rust_primitives.arithmetic.to_le_bytes_u128
  rust_primitives.arithmetic.to_le_bytes_usize

end CoreModels
