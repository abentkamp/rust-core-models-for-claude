import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-! ## `rust_primitives::arithmetic` little-endian byte conversions.

These are the primitive implementations behind `core::num`'s
`from_le_bytes`/`to_le_bytes` (see `Spec/Core/Num.lean`); registering them as
`[spec]` lets `mvcgen` step through the `core::num` wrappers. -/

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
