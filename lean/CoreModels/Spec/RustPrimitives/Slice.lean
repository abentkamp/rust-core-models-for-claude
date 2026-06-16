import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-- Helper lemma for the spec of `rust_primitives.slice.array_from_fn`. -/
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
    mvcgen [rust_primitives.slice.array_from_fn_go]
    refine ⟨trivial, rfl, ?_⟩
    intro i hi; exact absurd hi (by simp)
  | succ n ih =>
    -- Enrich `hpure` so each call's *value* (not just its state `r.2`) survives
    -- `mvcgen`: the extra conjunct pins the result via a self-referential triple.
    have hpure' := fun k hk c' hc' => triple_with_self (hpure k hk c' hc')
    mvcgen [rust_primitives.slice.array_from_fn_go, ih, hpure']
    case vc6 =>
      rename_i r_rec h_rec r_call h_call
      obtain ⟨h_receq, h_reclen, h_recpost⟩ := h_rec
      obtain ⟨h_call2, h_callself⟩ := h_call
      refine ⟨h_call2, by simp [h_reclen], ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · -- `i < n`: the `i`-th element comes from the recursion.
        rw [List.getElem_append_left (by omega)]
        exact h_recpost i hlt
      · -- `i = n`: the last element is `r_call.1`, pinned by `h_callself`.
        subst heq
        rw [← h_receq]
        mvcgen [h_callself]
        grind
    -- The remaining goals are the specs' premises (index bounds, state equality).
    all_goals grind

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
  -- The worker spec `array_from_fn_go_pure` (a `@[spec]`) is applied by `mvcgen`;
  -- `hpure'` supplies its (state-preservation) premise.
  have hpure' : ∀ k, k < N.val → ∀ c', c' = c →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c' ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄ :=
    fun k hk c' hc' => hc' ▸ hpure k hk
  mvcgen [rust_primitives.slice.array_from_fn, hpure']
  · -- then-branch: each cell is what the worker's nested triple produces.
    rename_i r hlen hconj
    obtain ⟨_, _, hpost⟩ := hconj
    intro i hi
    have hp := hpost i hi
    mvcgen [hp]
    grind
  · -- else-branch is impossible: the worker's length equals `N`.
    rename_i r hlen hconj
    obtain ⟨_, hlen', _⟩ := hconj
    exact absurd hlen' hlen

end CoreModels
