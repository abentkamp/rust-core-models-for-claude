import CoreModels.Spec.Aeneas
import CoreModels.Spec.RustPrimitives.Slice

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-! ### `core::convert`'s `TryFrom<&[T]> for [T; N]`
(`CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from`).

The body invokes `CoreModels.rust_primitives.slice.array_from_fn` on the `try_from`
closure (whose state is just the source `Slice T`). The proof has three
parts:

1. Closure step: `call_mut s i = .ok (s.val[i.val], s)` for `i.val <
   s.length` — the closure reads the slice and preserves its state.
2. Assembly via the shared `array_from_fn_spec` (see
   `Spec/RustPrimitives/Slice.lean`): the closure is pure with `f k = s.val[k]`,
   so `array_from_fn N closure s = .ok (Array.make N s.val)` when
   `s.length = N.val` (the image of `0 .. N` under `f` is `s.val`).
3. Final assembly: `try_from N inst s = .ok (.Ok a)` with `a.val = s.val`. -/

/-- Closure step lemma. The `try_from` closure's state is the source
    `Slice T`; `call_mut` reads the `i`-th element and preserves state.

    We state this on the unfolded form `...call_mut.call_mut cpy s i`
    because that's what the FnMut instance's `call_mut` field reduces to
    after Lean unfolds the structure projection. -/
private theorem Convert.try_from_slice_closure_eq
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (i : Std.Usize) (h : i.val < s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      (T := T) (N := N) cpy s i
    ⦃ ⇓ r => ⌜ r = (s.val[i.val]'h, s) ⌝ ⦄ := by
  unfold CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  unfold CoreModels.rust_primitives.slice.slice_index Std.Slice.index_usize
  -- `mvcgen` splits on `s[i]?`; for `i.val < s.length` it is `some s.val[i.val]`,
  -- so the out-of-bounds branch is impossible and the value matches.
  mvcgen <;> simp_all [Std.Slice.getElem?_Usize_eq]

/-- `array_from_fn N (try_from closure) s = .ok (Array.make N s.val)`
    when `s.length = N.val`.

    The `try_from` closure is pure — it reads `s` and preserves it — so this
    is the shared `array_from_fn_spec` instantiated at `f := fun k => s.val[k]`,
    whose image over `0 .. N` is exactly `s.val`. -/
theorem Convert.try_from_slice_array_from_fn_eq
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.rust_primitives.slice.array_from_fn N
      (CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        (T := T) (N := N) cpy) s
    ⦃ ⇓ a => ⌜ a = Std.Array.make N s.val (by simp [hlen]) ⌝ ⦄ := by
  have hN_max : N.val ≤ Std.Usize.max := by rw [← hlen]; exact s.property
  -- The closure reads `s` and preserves its state, so it is pure: `mvcgen`
  -- weakens the closure step `closure_eq` to its state-preservation part.
  have hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
        (T := T) (N := N) cpy s ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r.2 = s ⌝ ⦄ := by
    intro k hk
    have hval : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits k⟩ : Std.Usize).val = k := by
      grind [Nat.mod_eq_of_lt, Std.Usize.max_def, Std.Usize.numBits_def, UScalar.val]
    have hc := Convert.try_from_slice_closure_eq (T := T) (N := N) cpy s
                    ⟨BitVec.ofNat _ k⟩ (by rw [hval]; omega)
    mvcgen [hc]
    grind
  -- Apply the f-free `array_from_fn_spec` (a `@[spec]`) via `mvcgen`; each cell
  -- of the result `a` is what the closure produces, i.e. `s.val[i]`.
  mvcgen [hpure]
  rename_i a
  intro hapost
  apply Subtype.ext
  apply List.ext_getElem
  · rw [a.property]; exact hlen.symm
  · intro i h1 h2
    have hi : i < N.val := a.property ▸ h1
    have hval : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits i⟩ : Std.Usize).val = i := by
      grind [Nat.mod_eq_of_lt, Std.Usize.max_def, Std.Usize.numBits_def, UScalar.val]
    have hc := Convert.try_from_slice_closure_eq (T := T) (N := N) cpy s
                    ⟨BitVec.ofNat _ i⟩ (by rw [hval]; omega)
    -- Combine the cell triple (`hapost i`) with the closure's concrete value.
    have hcell := triple_ok_elim (hapost i hi) (result_eq_of_triple hc)
    simp only [Std.Array.make, hval] at hcell ⊢
    exact hcell.symm

/-- The main Triple: `try_from N cpy s` succeeds with `Ok (Array.make N s.val _)`,
    whenever `s.val.length = N.val`. -/
@[spec]
theorem Convert.try_from_slice_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = CoreModels.core.result.Result.Ok
                    (Std.Array.make N s.val (by simp [hlen])) ⌝ ⦄ := by
  -- `Slice.len s = N` reduces to `s.val.length = N.val`.
  have hi_eq : (Std.Slice.len s) = N := by
    apply Std.UScalar.eq_of_val_eq
    simp [hlen]
  -- Feed the exact-array spec `try_from_slice_array_from_fn_eq` to `mvcgen`
  -- (the f-free `@[spec]` can't pin the resulting array on its own).
  have h_afn := Convert.try_from_slice_array_from_fn_eq (T := T) (N := N) cpy s hlen
  mvcgen [CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
    CoreModels.core.slice.Slice.len, h_afn, -array_from_fn_spec]
  grind

end CoreModels
