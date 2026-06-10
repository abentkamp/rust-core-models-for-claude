import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas


namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Std.Do Result
set_option mvcgen.warning false

open ScalarElab

uscalar @[spec] theorem «%S».Core_modelsCmpPartialEqArray.eq_spec {N : Std.Usize} {Q}
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
theorem core_models_Array_Insts_index_RangeUsize_spec
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

private theorem from_fn_foldlM_pure_aux
    {T F : Type}
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (l : List Nat) (acc : List T)
    (hpure : ∀ k ∈ l,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    l.foldlM
      (fun (s : List T × F) (i : Nat) => do
        let (v, f') ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
        Result.ok (s.1 ++ [v], f'))
      (acc, c) = .ok (acc ++ l.map f, c) := by
  induction l generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, List.map_nil, List.append_nil]; rfl
  | cons h t ih =>
      have hh : inst.call_mut c ⟨BitVec.ofNat _ h⟩ = .ok (f h, c) :=
        hpure h List.mem_cons_self
      have ht : ∀ k ∈ t, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (List.mem_cons_of_mem _ hk)
      have hih := ih (acc ++ [f h]) ht
      simp only [List.foldlM_cons, hh, bind_tc_ok, List.map_cons]
      rw [hih]
      simp [List.append_assoc]

/-- Lean-level equation for `from_fn` over pure closures. -/
private theorem from_fn_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    CoreModels.core.array.from_fn N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    from_fn_foldlM_pure_aux inst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold CoreModels.core.array.from_fn CoreModels.rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = ((List.range N.val).map f, c) :=
      (Result.ok.inj heq).symm
    subst hres
    rfl


/-- **Generic pure-closure `[spec]` for `core_models.array.from_fn`.**

For any closure whose `call_mut` is pure (doesn't mutate state),
`from_fn N inst c` succeeds and its `i`-th cell is `f i`. `hpure` is a
Triple over each `call_mut` so `hax_mvcgen` can recurse through it via
per-closure `@[spec]` lemmas. -/
@[spec]
theorem from_fn_pure_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      inst.call_mut c ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    core.array.from_fn N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val → a.val[i]! = f i ⌝ ⦄ := by
  have hpure_eq : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
    sorry -- fun k hk => result_eq_of_triple (hpure k hk)
  have heq := from_fn_pure_eq N inst c f hpure_eq
  rw [heq]
  simp only [Triple, WP.wp]
  apply SPred.pure_intro
  intro i hi
  show ((List.range N.val).map f)[i]! = f i
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi]
  rfl

end CoreModels
