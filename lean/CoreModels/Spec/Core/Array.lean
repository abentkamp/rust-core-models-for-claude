import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas
import CoreModels.Spec.RustPrimitives.Slice

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result
set_option mvcgen.warning false

open ScalarElab

uscalar @[spec] theorem «%S».Array.eq_spec {N : Std.Usize} {Q}
  (a : Array «%S» N) (b : Array «%S» N) (h : (Q.1 (a.val == b.val)).down) :
  ⦃ ⌜ True ⌝ ⦄
  core.Array.Insts.CoreCmpPartialEqArray.eq core.«%S».Insts.CoreCmpPartialEq'S a b
  ⦃ Q ⦄ := by
  mvcgen -trivial [core.Array.Insts.CoreCmpPartialEqArray.eq,
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop,
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body, rust_primitives.slice.array_index,
    core.«%S».Insts.CoreCmpPartialEq'S]
  case vc1.γ => exact Nat
  case vc4.termination => exact fun i => N.val - i.val
  case vc3.rel => exact (· < ·)
  case vc5.hwf => exact wellFounded_lt
  case vc2.inv => exact fun i => a.val.take i.val = b.val.take i.val
  case vc10 =>
    constructor
    · simp_all [@List.take_add, @List.take_one, -List.take_append_getElem]
    · grind
  · grind
  · grind
  · grind
  · grind
  · convert h; grind
  · convert h; grind [List.take_eq_self_iff, List.Vector.length_val]

@[spec]
theorem Array.index_range_spec
      {T : Type} {N : Std.Usize} (arr : Std.Array T N)
      (r : core.ops.range.Range Std.Usize)
      (h0 : r.start.val < r.end.val) -- TODO: We should be able to allow "≤" here
      (h1 : r.end.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndexRangeUsizeSlice.index arr r
    ⦃ ⇓ r' => ⌜ r'.val = arr.val.slice r.start.val r.end.val ∧
                r'.val.length + r.start.val = r.end.val ⌝ ⦄ := by
  mvcgen [core.Array.Insts.CoreOpsIndexIndexRangeUsizeSlice.index,
    rust_primitives.slice.array_slice, -Array.subslice_spec.mvcgen_spec, Array.subslice]
    <;> grind


/-! ## A generic `from_fn` pure-closure spec.

Analogous to `createi_pure_spec` (HacspecBridge.lean:663) but takes
a `FnMut` instance directly (no `Fn` wrapper). Required because
`sponge.xor_block_into_state` calls `CoreModels.core.array.from_fn` directly
with the `FnMut` instance of its closure. -/

/-- **Generic pure-closure `[spec]` for `core_models.array.from_fn`.**

For any closure whose `call_mut` is pure (doesn't mutate state),
`from_fn N inst c` succeeds and its `i`-th cell is `f i`. `hpure` is a
Triple over each `call_mut` so `hax_mvcgen` can recurse through it via
per-closure `@[spec]` lemmas. -/
@[spec]
theorem Array.from_fn_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      inst.call_mut c ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    core.array.from_fn N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val → a.val[i]! = f i ⌝ ⦄ := by
  unfold CoreModels.core.array.from_fn
  mvcgen
  case vc1.hpure =>
    rename_i k hk
    rw [result_eq_of_triple (hpure k hk)]
    simp [WP.wp, PredTrans.apply]
  case vc2.success =>
    intro hpost i hi
    exact (triple_ok_elim (hpost i hi) (result_eq_of_triple (hpure i hi))).symm

end CoreModels
