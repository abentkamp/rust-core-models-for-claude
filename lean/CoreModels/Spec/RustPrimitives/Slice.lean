import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-! ## Generic pure-closure reasoning for `rust_primitives::slice::array_from_fn`.

`array_from_fn` builds an array by threading a `FnMut` closure across `0 .. N`
(via the recursive worker `array_from_fn_go`). When that closure is *pure* —
`call_mut c i = .ok (f i, c)` for some `f : Nat → T`, leaving the state `c`
untouched — the result is just `.ok (List.range N |>.map f)`. Both
`core.array.from_fn` (see `Spec/Core/Array.lean`) and the slice→array
`core.convert` `try_from` (see `Spec/Core/Convert.lean`) are instances of this
pattern, so the recursion lives here once. -/

/-- The recursive worker over a pure closure returns `l.map f`. -/
private theorem array_from_fn_go_pure
    {T F : Type}
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T) (l : List Nat)
    (hpure : ∀ k ∈ l, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    rust_primitives.slice.array_from_fn_go inst c l = .ok (l.map f) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    -- Restate the goal in this lemma's elaboration context so the `Usize`
    -- index width lines up syntactically with `hpure` (the worker's `_`
    -- elaborates to a defeq-but-distinct width).
    show (do
      let p ← inst.call_mut c ⟨BitVec.ofNat _ h⟩
      let r ← rust_primitives.slice.array_from_fn_go inst p.2 t
      ok (p.1 :: r)) = .ok ((h :: t).map f)
    rw [hpure h List.mem_cons_self]
    simp [bind_tc_ok, ih (fun k hk => hpure k (List.mem_cons_of_mem _ hk)), List.map_cons]

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
  have hgo := array_from_fn_go_pure inst c f (List.range N.val)
    (fun k hk => hpure k (List.mem_range.mp hk))
  unfold CoreModels.rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [hgo] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [hgo] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [hgo] at heq
    have hres : result = (List.range N.val).map f := (Result.ok.inj heq).symm
    subst hres
    rfl

end CoreModels
