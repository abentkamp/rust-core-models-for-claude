/-
  Scalar trait instances for the Aeneas library.
  Imported after Types.lean which provides the trait structure definitions.
-/
import CoreModels.Types
import CoreModels.Alloc.Types

namespace core_models

open Aeneas.Std Result

/-! ## Scalar PartialEq / PartialOrd instances -/

instance U8.Insts.Core_modelsCmpPartialEqU8       : cmp.PartialEq U8    U8    := { eq := fun x y => ok (x == y) }
instance U16.Insts.Core_modelsCmpPartialEqU16     : cmp.PartialEq U16   U16   := { eq := fun x y => ok (x == y) }
instance U32.Insts.Core_modelsCmpPartialEqU32     : cmp.PartialEq U32   U32   := { eq := fun x y => ok (x == y) }
instance U64.Insts.Core_modelsCmpPartialEqU64     : cmp.PartialEq U64   U64   := { eq := fun x y => ok (x == y) }
instance U128.Insts.Core_modelsCmpPartialEqU128   : cmp.PartialEq U128  U128  := { eq := fun x y => ok (x == y) }
instance Usize.Insts.Core_modelsCmpPartialEqUsize : cmp.PartialEq Usize Usize := { eq := fun x y => ok (x == y) }
instance I8.Insts.Core_modelsCmpPartialEqI8       : cmp.PartialEq I8    I8    := { eq := fun x y => ok (x == y) }
instance I16.Insts.Core_modelsCmpPartialEqI16     : cmp.PartialEq I16   I16   := { eq := fun x y => ok (x == y) }
instance I32.Insts.Core_modelsCmpPartialEqI32     : cmp.PartialEq I32   I32   := { eq := fun x y => ok (x == y) }
instance I64.Insts.Core_modelsCmpPartialEqI64     : cmp.PartialEq I64   I64   := { eq := fun x y => ok (x == y) }
instance I128.Insts.Core_modelsCmpPartialEqI128   : cmp.PartialEq I128  I128  := { eq := fun x y => ok (x == y) }
instance Isize.Insts.Core_modelsCmpPartialEqIsize : cmp.PartialEq Isize Isize := { eq := fun x y => ok (x == y) }

/-! ## Slice -/

def slice.Slice.len {T : Type u} (v : Aeneas.Std.Slice T) : Aeneas.Std.Result Usize :=
  pure (@Aeneas.Std.Slice.len T v)

/-! ## Option -/

def option.Option.unwrap_or :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.unwrap_or T x y)

def option.Option.is_some :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_some T x)

def option.Option.is_none :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_none T x)

def option.Option.take :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.take T x)

/-! ## Mem -/

def mem.swap :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.swap T x y)

def mem.replace :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.replace T x y)

/-! ## Redirects to Aeneas's library -/

export Aeneas.Std.core (
  num.U8.MIN num.U8.MAX num.I8.MIN num.I8.MAX
  num.U16.MIN num.U16.MAX num.I16.MIN num.I16.MAX
  num.U32.MIN num.U32.MAX num.I32.MIN num.I32.MAX
  num.U64.MIN num.U64.MAX num.I64.MIN num.I64.MAX
  num.U128.MIN num.U128.MAX num.I128.MIN num.I128.MAX
  num.Usize.MIN num.Usize.MAX num.Isize.MIN num.Isize.MAX
  convert.num.FromU16U8.from
  convert.num.FromU32U8.from
  convert.num.FromU32U16.from
  convert.num.FromU64U8.from
  convert.num.FromU64U16.from
  convert.num.FromU64U32.from
  convert.num.FromU128U8.from
  convert.num.FromU128U16.from
  convert.num.FromU128U32.from
  convert.num.FromU128U64.from
  convert.num.FromUsizeU8.from
  convert.num.FromUsizeU16.from
  convert.num.FromI16I8.from
  convert.num.FromI32I8.from
  convert.num.FromI32I16.from
  convert.num.FromI64I8.from
  convert.num.FromI64I16.from
  convert.num.FromI64I32.from
  convert.num.FromI128I8.from
  convert.num.FromI128I16.from
  convert.num.FromI128I32.from
  convert.num.FromI128I64.from
  convert.num.FromIsizeI8.from
  convert.num.FromIsizeI16.from
)

end core_models
