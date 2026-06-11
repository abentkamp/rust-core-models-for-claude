import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-! ## Generic pure-closure reasoning for `rust_primitives::slice::array_from_fn`.

`array_from_fn` folds a `FnMut` closure across `0 .. N`. When that closure is
*pure* — `call_mut c i = .ok (f i, c)` for some `f : Nat → T`, leaving the
state `c` untouched — the whole fold collapses to `.ok (List.range N |>.map f)`.
Both `core.array.from_fn` (see `Spec/Core/Array.lean`) and the slice→array
`core.convert` `try_from` (see `Spec/Core/Convert.lean`) are instances of this
pattern, so the fold induction lives here once. -/

/-- The closure-fold accumulator after folding a pure closure over `l` is
    `acc ++ l.map f`. Generic over the closure `inst`/`c` and the pure
    function `f` it realizes. -/
private theorem array_from_fn_foldlM_pure
    {T F : Type}
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
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

/-- Lean-level equation for `array_from_fn` over a pure closure: the result is
    the array whose `i`-th cell is `f i`. -/
theorem array_from_fn_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    rust_primitives.slice.array_from_fn N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    array_from_fn_foldlM_pure inst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold CoreModels.rust_primitives.slice.array_from_fn
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

end CoreModels
