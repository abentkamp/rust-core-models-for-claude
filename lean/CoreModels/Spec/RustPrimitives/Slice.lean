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
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (l : List Nat)
    (hpure : ∀ k ∈ l, ∀ c', c' = c →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c' ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn_go inst c l
    ⦃ ⇓ r => ⌜ ∃ h : r.length = l.length, ∀ i, (hi : i < l.length) →
                ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ i⟩
                          ⦃ ⇓ r' => ⌜ r[i] = r'.1 ⌝ ⦄ ⌝ ⦄ := by
  induction l generalizing c with
  | nil =>
    mvcgen [rust_primitives.slice.array_from_fn_go]; grind
  | cons h t ih =>
    have hh := hpure h List.mem_cons_self
    unfold rust_primitives.slice.array_from_fn_go
    mvcgen [ih, hpure]
    grind
    grind
    grind
    grind
    rename_i h
    cases h with
    | intro hlen h =>
      use (by grind)
      intros i hi
      sorry

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
  -- Extract the value function `f` the closure realizes.
  -- have hex : ∀ k, k < N.val → ∃ v : T, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (v, c) := by
  --   intro k hk
  --   obtain ⟨⟨v, st⟩, hok, hst⟩ := exists_ok_of_triple (hpure k hk)
  --   have : st = c := hst
  --   exact ⟨v, this ▸ hok⟩
  -- classical
  -- let f : Nat → T := fun k => if h : k < N.val then (hex k h).choose else default
  -- have hf : ∀ k : Nat, k < N.val → inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
  --   intro k hk
  --   show inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok ((dite _ (fun h => (hex k h).choose) _), c)
  --   rw [dif_pos hk]
  --   exact (hex k hk).choose_spec
  mvcgen [rust_primitives.slice.array_from_fn, hpure]
  · grind +suggestions
  · grind +suggestions
  · grind
  · grind
  rintro rfl i hi
  apply triple_ok_intro (hf i hi)
  show f i = ((List.range N.val).map f)[i]!
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

end CoreModels
