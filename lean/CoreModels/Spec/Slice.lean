import CoreModels.Spec.Aeneas
import CoreModels.Spec.FromFn

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

attribute [spec]
  CoreModels.core.slice.Slice.len
  massert
  CoreModels.core.num.U8.from_le_bytes
  CoreModels.core.num.U16.from_le_bytes
  CoreModels.core.num.U32.from_le_bytes
  CoreModels.core.num.U64.from_le_bytes
  CoreModels.core.num.U128.from_le_bytes
  CoreModels.core.num.Usize.from_le_bytes
  CoreModels.core.num.U8.to_le_bytes
  CoreModels.core.num.U16.to_le_bytes
  CoreModels.core.num.U32.to_le_bytes
  CoreModels.core.num.U64.to_le_bytes
  CoreModels.core.num.U128.to_le_bytes
  CoreModels.core.num.Usize.to_le_bytes
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

@[spec]
theorem CoreOpsIndexIndexRangeUsizeSlice_index_spec
    {T : Type} (s : Slice T) (r : core.ops.range.Range Std.Usize)
    (h0 : r.start.val < r.end.val) -- TODO: we should be able to allow "≤"
    (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.Shared0Slice.Insts.CoreOpsIndexIndexRangeUsizeSlice.index s r
    ⦃ ⇓ r' => ⌜ r'.val = s.val.slice r.start.val r.end.val ∧
                r.start.val + r'.val.length = r.end.val ⌝ ⦄ := by
  mvcgen [core.Shared0Slice.Insts.CoreOpsIndexIndexRangeUsizeSlice.index,
    rust_primitives.slice.slice_slice, -Slice.subslice_spec.mvcgen_spec, Slice.subslice]
    <;> grind


/-! ### `CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from`

The body invokes `CoreModels.rust_primitives.slice.array_from_fn` on the `try_from`
closure (whose state is just the source `Slice T`). The proof has three
parts:

1. Closure step: `call_mut s i = .ok (s.val[i.val]!, s)` for `i.val <
   s.length` — the closure reads the slice and preserves its state.
2. Assembly via the shared `array_from_fn_pure_eq` (see `Spec/FromFn.lean`):
   the closure is pure with `f k = s.val[k]!`, so
   `array_from_fn N closure s = .ok (Array.make N s.val)` when
   `s.length = N.val` (the image of `0 .. N` under `f` is `s.val`).
3. Final assembly: `try_from N inst s = .ok (.Ok a)` with `a.val = s.val`. -/

/-- Closure step lemma. The `try_from` closure's state is the source
    `Slice T`; `call_mut` reads the `i`-th element and preserves state.

    We state this on the unfolded form `...call_mut.call_mut cpy s i`
    because that's what the FnMut instance's `call_mut` field reduces to
    after Lean unfolds the structure projection. -/
private theorem try_from_closure_call_mut_eq
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (i : Std.Usize) (h : i.val < s.val.length) :
    CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      (T := T) (N := N) cpy s i =
      .ok (s.val[i.val]!, s) := by
  -- Reduces to `do let t ← slice_index s i; ok (t, s)`.
  unfold CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  unfold CoreModels.rust_primitives.slice.slice_index Std.Slice.index_usize
  -- Now `s[i]?` matches; for `i.val < s.length`, `s[i]? = some s.val[i.val]!`.
  have hsome : s[i]? = some s.val[i.val]! := by
    simp only [Std.Slice.getElem?_Usize_eq]
    rw [List.getElem?_eq_getElem h, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem h]
    rfl
  rw [hsome]
  rfl

/-- `array_from_fn N (try_from closure) s = .ok (Array.make N s.val)`
    when `s.length = N.val`.

    The `try_from` closure is pure — it reads `s` and preserves it — so this
    is the shared `array_from_fn_pure_eq` instantiated at `f := fun k => s.val[k]!`,
    whose image over `0 .. N` is exactly `s.val`. -/
theorem array_from_fn_try_from_eq_ok
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    CoreModels.rust_primitives.slice.array_from_fn N
      (CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        (T := T) (N := N) cpy) s
    = .ok (Std.Array.make N s.val (by simp [hlen])) := by
  have hN_max : N.val ≤ Std.Usize.max := by rw [← hlen]; exact s.property
  -- The closure realizes the pure function `f k = s.val[k]!`.
  have hpure : ∀ k : Nat, k < N.val →
      CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
        (T := T) (N := N) cpy s ⟨BitVec.ofNat _ k⟩ = .ok (s.val[k]!, s) := by
    intro k hk
    have hk_len : k < s.val.length := by omega
    have hval : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits k⟩ : Std.Usize).val = k := by
      grind [Nat.mod_eq_of_lt, Std.Usize.max_def, Std.Usize.numBits_def, UScalar.val]
    have hcall := try_from_closure_call_mut_eq (T := T) (N := N) cpy s
                    ⟨BitVec.ofNat _ k⟩ (by rw [hval]; exact hk_len)
    rw [hval] at hcall; exact hcall
  have heq := array_from_fn_pure_eq (T := T) N
                (CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
                  (T := T) (N := N) cpy) s (fun k => s.val[k]!) hpure
  rw [heq]
  -- The image of `0 .. N` under `k ↦ s.val[k]!` is `s.val` itself.
  have hmap : (List.range N.val).map (fun k => s.val[k]!) = s.val := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i _ h2
      simp [List.getElem_map, List.getElem_range, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem h2]
  simp only [hmap, Std.Array.make]

/-- The main Triple: `try_from N cpy s` succeeds with `Ok (Array.make N s.val _)`,
    whenever `s.val.length = N.val`. -/
@[spec]
theorem core_models_array_try_from_slice_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = CoreModels.core.result.Result.Ok
                    (Std.Array.make N s.val (by simp [hlen])) ⌝ ⦄ := by
  -- Unfold try_from and reduce the `do` chain step-by-step.
  unfold CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  -- `CoreModels.core.slice.Slice.len x` is `pure (Slice.len x)`, returns `.ok (Slice.len s)`.
  unfold CoreModels.core.slice.Slice.len
  -- The if-decision: `Slice.len s = N` reduces to `s.val.length = N.val`.
  have hi_eq : (Std.Slice.len s) = N := by
    apply Std.UScalar.eq_of_val_eq
    simp [hlen]
  -- Reduce the array_from_fn call to .ok.
  have h_afn := array_from_fn_try_from_eq_ok (T := T) (N := N) cpy s hlen
  simp only [Triple, WP.wp, Pure.pure, bind_tc_ok, hi_eq, if_true, h_afn]
  intro _
  trivial
