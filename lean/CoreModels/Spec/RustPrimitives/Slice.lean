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
    refine triple_ok_intro rfl ⟨rfl, rfl, ?_⟩
    intro i hi; exact absurd hi (by simp)
  | succ n ih =>
    obtain ⟨p, hp, hp2, hplen, hppost⟩ :=
      exists_ok_of_triple (ih c (fun k hk c' hc' => hpure k (Nat.lt_succ_of_lt hk) c' hc'))
    obtain ⟨q, hq, hq2⟩ := exists_ok_of_triple (hpure n (Nat.lt_succ_self n) p.2 hp2)
    have hgo : rust_primitives.slice.array_from_fn_go inst c (n + 1)
        = .ok (p.1 ++ [q.1], q.2) := by
      simp only [rust_primitives.slice.array_from_fn_go, hp, bind_tc_ok, hq]
    refine triple_ok_intro hgo ⟨hq2, by simp [hplen], ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · -- `i < n`: the `i`-th element comes from `p.1`.
      have hidx : (p.1 ++ [q.1])[i]'(by simp [hplen]; omega) = p.1[i]'(by omega) :=
        List.getElem_append_left (by omega)
      rw [hidx]; exact hppost i hlt
    · -- `i = n`: the last element is `q.1`.
      subst heq
      have hidx : (p.1 ++ [q.1])[i]'(by simp [hplen]) = q.1 := by
        rw [List.getElem_append_right (by omega)]; simp [hplen]
      rw [hidx]; exact triple_ok_intro (hp2 ▸ hq) rfl

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
