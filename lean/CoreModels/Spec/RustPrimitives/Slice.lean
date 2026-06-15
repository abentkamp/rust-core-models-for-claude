import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-- Helper lemma for the spec of `rust_primitives.slice.array_from_fn`.

The closure is called at the indices listed in `l` (the worker folds over `l`),
so the `i`-th result element is the value `call_mut` produces at index `l[i]`. -/
@[spec]
theorem array_from_fn_go_pure
    {T F : Type}
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (l : List Nat)
    (hpure : ∀ k ∈ l, ∀ c', c' = c →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c' ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn_go inst c l
    ⦃ ⇓ r => ⌜ ∃ h : r.length = l.length, ∀ i, (hi : i < l.length) →
                ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ l[i]⟩
                          ⦃ ⇓ r' => ⌜ r[i] = r'.1 ⌝ ⦄ ⌝ ⦄ := by
  induction l generalizing c with
  | nil =>
    refine triple_ok_intro rfl ⟨rfl, ?_⟩
    intro i hi; exact absurd hi (by simp)
  | cons h t ih =>
    obtain ⟨p, hp, hp2⟩ := exists_ok_of_triple (hpure h List.mem_cons_self c rfl)
    obtain ⟨rt, hrt, htlen, htpost⟩ :=
      exists_ok_of_triple (ih c (fun k hk c' hc' => hpure k (List.mem_cons_of_mem _ hk) c' hc'))
    have hgo : rust_primitives.slice.array_from_fn_go inst c (h :: t) = .ok (p.1 :: rt) := by
      simp only [rust_primitives.slice.array_from_fn_go, hp, bind_tc_ok, hp2, hrt]
    refine triple_ok_intro hgo ⟨by simp [htlen], ?_⟩
    intro i hi
    rcases i with _ | j
    · simp only [List.getElem_cons_zero]
      exact triple_ok_intro hp rfl
    · have hj : j < t.length := by simpa using hi
      simp only [List.getElem_cons_succ]
      exact htpost j hj

/-- This spec assumes that the closure is not mutated. If the closure was mutated,
we would need a more complex spec that would require the user to provide an invariant. -/
@[spec]
theorem array_from_fn_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val →
                ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ i⟩
                          ⦃ ⇓ r => ⌜ r.1 = a.val[i]! ⌝ ⦄ ⌝ ⦄ := by
  -- `array_from_fn` folds over `List.range N.val`, where the index equals the
  -- position, so `array_from_fn_go_pure` directly characterizes each cell.
  obtain ⟨r, hr, hrlen, hrpost⟩ := exists_ok_of_triple
    (array_from_fn_go_pure inst c (List.range N.val)
      (fun k hk c' hc' => hc' ▸ hpure k (List.mem_range.mp hk)))
  have hrlen' : r.length = N.val := by simpa using hrlen
  have haf : rust_primitives.slice.array_from_fn N inst c = .ok ⟨r, by simp [hrlen']⟩ := by
    simp only [rust_primitives.slice.array_from_fn, hr, bind_tc_ok]
    rw [dif_pos (by simp [hrlen'])]
  refine triple_ok_intro haf ?_
  intro i hi
  obtain ⟨v, hv, hvval⟩ := exists_ok_of_triple (hrpost i (by simpa using hi))
  simp only [List.getElem_range] at hv
  refine triple_ok_intro hv ?_
  show v.1 = r[i]!
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show i < r.length by omega),
    Option.getD_some]
  exact hvval.symm

end CoreModels
