import CoreModels.Spec.Aeneas
import CoreModels.Spec.RustPrimitives.Slice

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

@[spec]
theorem Convert.try_from_slice_spec_closure
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (i : Std.Usize) (h : i.val < s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      (T := T) (N := N) cpy s i
    ⦃ ⇓ r => ⌜ r = (s.val[i.val]'h, s) ⌝ ⦄ := by
  unfold CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  unfold CoreModels.rust_primitives.slice.slice_index Std.Slice.index_usize
  mvcgen <;> simp_all [Std.Slice.getElem?_Usize_eq]

@[spec]
theorem Convert.try_from_slice_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = CoreModels.core.result.Result.Ok
                    (Std.Array.make N s.val (by simp [hlen])) ⌝ ⦄ := by
  mvcgen [CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
    CoreModels.core.slice.Slice.len]
  · grind [UScalar.val]
  · grind
  · rename_i a hapost
    congr
    apply Subtype.ext
    apply List.ext_getElem
    · rw [a.property]; exact hlen.symm
    · intro i h1 h2 -- TODO: use triple from hyp, and then mvcgen.
      apply triple_in_hypothesis _ (hapost i (a.property ▸ h1))
      mvcgen <;> grind [UScalar.val, Array.make]
  · grind

end CoreModels
