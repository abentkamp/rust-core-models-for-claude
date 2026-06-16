import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-- Helper lemma for the spec of `rust_primitives.slice.array_from_fn`.

The closure is called at the indices `0, 1, …, n-1` (in order, threading state),
so the `i`-th result element is the value `call_mut` produces at index `i`. For a
pure closure (state preserved) the final state `r.2` is unchanged. -/
@[spec]
theorem array_from_fn_go_pure
    {T F : Type}
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (n : Nat)
    (hpure : ∀ k, k < n → ∀ c', c' = c →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c' ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn_go inst c n
    ⦃ ⇓ r => ⌜ r.2 = c ∧ ∃ h : r.1.length = n, ∀ i, (hi : i < n) →
                ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ i⟩
                          ⦃ ⇓ r' => ⌜ r.1[i] = r'.1 ⌝ ⦄ ⌝ ⦄ := by
  induction n generalizing c with
  | zero =>
    -- `array_from_fn_go inst c 0 = ok ([], c)`; `mvcgen` reduces the triple to
    -- its (vacuous) postcondition.
    mvcgen [rust_primitives.slice.array_from_fn_go]
    refine ⟨trivial, rfl, ?_⟩
    intro i hi; exact absurd hi (by simp)
  | succ n ih =>
    -- Enrich `hpure` so each call's *value* (not just its state `r.2`) survives
    -- `mvcgen`: the extra conjunct pins the result via a self-referential triple.
    have hpure' : ∀ k, k < n + 1 → ∀ c', c' = c →
        ⦃ ⌜ True ⌝ ⦄ inst.call_mut c' ⟨BitVec.ofNat _ k⟩
        ⦃ ⇓ r => ⌜ r.2 = c ∧
            ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r' => ⌜ r' = r ⌝ ⦄ ⌝ ⦄ := by
      intro k hk c' hc'; subst c'
      exact triple_with_self (hpure k hk c rfl)
    mvcgen [rust_primitives.slice.array_from_fn_go, ih, hpure']
    -- The final verification condition: the recursion (`h_rec`) handles indices
    -- `< n`, and the enriched closure spec (`h_callself`) pins the last element.
    case vc6 =>
      rename_i r_rec h_rec r_call h_call
      obtain ⟨_, h_reclen, h_recpost⟩ := h_rec
      obtain ⟨h_call2, h_callself⟩ := h_call
      refine ⟨h_call2, by simp [h_reclen], ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · -- `i < n`: the `i`-th element comes from the recursion.
        rw [List.getElem_append_left (by omega)]
        exact h_recpost i hlt
      · -- `i = n`: the last element is `r_call.1`, pinned by `h_callself`.
        subst heq
        rw [show (r_rec.1 ++ [r_call.1])[i]'(by simp [h_reclen]) = r_call.1 by
              rw [List.getElem_append_right (by omega)]; simp [h_reclen]]
        mvcgen [h_callself]
        rintro rfl; rfl
    -- The remaining goals are the specs' premises (index bounds, state equality).
    all_goals first | omega | tauto

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
    ⦃ ⇓ a => ⌜ ∀ i : Nat, (hi : i < N.val) →
                ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ i⟩
                          ⦃ ⇓ r => ⌜ r.1 = a.val[i]'(by have := a.property; omega) ⌝ ⦄ ⌝ ⦄ := by
  -- `array_from_fn` runs the worker over `0 .. N.val`, where the index equals
  -- the position, so `array_from_fn_go_pure` directly characterizes each cell.
  obtain ⟨r, hr, _, hrlen, hrpost⟩ := exists_ok_of_triple
    (array_from_fn_go_pure inst c N.val
      (fun k hk c' hc' => hc' ▸ hpure k hk))
  have haf : rust_primitives.slice.array_from_fn N inst c = .ok ⟨r.1, hrlen⟩ := by
    simp only [rust_primitives.slice.array_from_fn, hr, bind_tc_ok]
    rw [dif_pos hrlen]
  refine triple_ok_intro haf ?_
  intro i hi
  obtain ⟨v, hv, hvval⟩ := exists_ok_of_triple (hrpost i hi)
  exact triple_ok_intro hv hvval.symm

end CoreModels
