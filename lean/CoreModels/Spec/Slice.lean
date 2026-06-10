import CoreModels.Spec.Aeneas

namespace CoreModels


open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Std.Do Result

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
2. `foldlM` invariant: induction on `k` shows that folding the closure
   over `List.range' 0 k` (starting from `([], s)`) returns
   `(s.val.take k, s)` when `k ≤ s.length`.
3. Final assembly: `array_from_fn N closure s = .ok (Array.make N s.val)`
   when `s.length = N.val`, hence `try_from N inst s = .ok (.Ok a)` with
   `a.val = s.val`. -/

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

/-- The closure-fold accumulator at step `k` is `s.val.take k`. We prove
    a slightly stronger invariant: starting from any accumulator `acc`
    with the closure state `s`, folding over `List.range' acc.length k`
    yields `(acc ++ s.val.slice acc.length (acc.length + k), s)` when
    `acc.length + k ≤ s.length` and acc lines up with the slice prefix. -/
private theorem foldlM_try_from_closure_invariant
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T)
    (_hN : s.val.length ≤ Std.Usize.max) :
    ∀ (k start : Nat) (acc : List T),
      acc = s.val.take start →
      start + k ≤ s.val.length →
      start + k ≤ Std.Usize.max →
      (List.range' start k).foldlM
        (fun (p : List T × Slice T) (i : Nat) => do
          let (v, f') ←
            CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
              (T := T) (N := N) cpy p.2 ⟨BitVec.ofNat _ i⟩
          ok (p.1 ++ [v], f'))
        (acc, s)
      = .ok (s.val.take (start + k), s) := by
  intro k
  induction k with
  | zero =>
    intro start acc hacc hk1 hk2
    show List.foldlM _ (acc, s) (List.range' start 0) = _
    rw [show List.range' start 0 = [] from rfl]
    rw [List.foldlM_nil]
    show Result.ok (acc, s) = Result.ok (s.val.take (start + 0), s)
    rw [hacc, Nat.add_zero]
  | succ k ih =>
    intro start acc hacc hk1 hk2
    -- `List.range' start (k+1) = start :: List.range' (start+1) k`
    rw [show List.range' start (k + 1) = start :: List.range' (start + 1) k from rfl]
    simp only [List.foldlM_cons]
    -- The step at `start` calls `call_mut s ⟨BitVec.ofNat _ start⟩`.
    have hstart_lt : start < s.val.length := by omega
    have hstart_max : start ≤ Std.Usize.max := by omega
    have hval : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits start⟩ : Std.Usize).val = start := by
      grind [Nat.mod_eq_of_lt, Std.Usize.max_def, Std.Usize.numBits_def, UScalar.val]
    have hcall := try_from_closure_call_mut_eq (T := T) (N := N) cpy s
                    ⟨BitVec.ofNat _ start⟩ (by rw [hval]; exact hstart_lt)
    -- Rewrite both the closure-call output's `.val` and the `i` arg uniformly.
    rw [hval] at hcall
    rw [hcall]
    simp only [bind_tc_ok]
    -- New accumulator is `acc ++ [s.val[start]!] = s.val.take (start + 1)`.
    have hacc' : acc ++ [s.val[start]!] = s.val.take (start + 1) := by
      rw [hacc]
      have : start < s.val.length := hstart_lt
      rw [List.take_add_one]
      simp [List.getElem?_eq_getElem this, List.getElem!_eq_getElem?_getD]
    -- Now apply IH at `start := start + 1`. Note `(start + 1) + k = start + (k + 1)`.
    have ih' := ih (start + 1) (acc ++ [s.val[start]!]) hacc' (by omega) (by omega)
    have h_assoc : (start + 1) + k = start + (k + 1) := by omega
    rw [h_assoc] at ih'
    exact ih'

/-- `array_from_fn N (try_from closure) s = .ok (Array.make N s.val)`
    when `s.length = N.val`. -/
theorem array_from_fn_try_from_eq_ok
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    CoreModels.rust_primitives.slice.array_from_fn N
      (CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        (T := T) (N := N) cpy) s
    = .ok (Std.Array.make N s.val (by simp [hlen])) := by
  -- Foldl invariant at start=0, k=N.val, acc=[].
  have hN_max : s.val.length ≤ Std.Usize.max := by
    have := s.property; exact this
  have hN_max' : N.val ≤ Std.Usize.max := by
    rw [← hlen]; exact hN_max
  have h_fold :=
    foldlM_try_from_closure_invariant (T := T) (N := N) cpy s hN_max
      N.val 0 [] (by simp) (by omega) (by omega)
  -- Normalize `0 + N.val = N.val` and reduce `take N.val s.val = s.val`.
  simp only [Nat.zero_add] at h_fold
  have h_take : s.val.take N.val = s.val :=
    List.take_of_length_le (by omega)
  rw [h_take] at h_fold
  -- Match `range N.val` with `range' 0 N.val` (`range` is defined as `range' 0 _`).
  have hrange : (List.range N.val) = List.range' 0 N.val := List.range_eq_range'
  -- The `array_from_fn` definition is a `match` on the foldlM result.
  -- We can't `rw [hrange]` (dependent motive); instead transfer h_fold to the
  -- `List.range` form first, then unfold and split.
  rw [← hrange] at h_fold
  unfold CoreModels.rust_primitives.slice.array_from_fn
  -- Now transport the foldlM equation through the `split`.
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = (s.val, s) := (Result.ok.inj heq).symm
    subst hres
    rfl

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
