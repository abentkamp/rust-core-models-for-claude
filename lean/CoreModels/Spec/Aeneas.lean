import CoreModels.Core.Funs

namespace Aeneas.Std
open Std.Do WP Result

set_option mvcgen.warning false

@[spec]
theorem Result.ok_spec {α : Type} {a : α} {Q} (hQ : (Q.1 a).down) :
  ⦃ ⌜ True ⌝ ⦄ Result.ok a ⦃ Q ⦄ := by simpa [Triple]

@[spec]
theorem Result.fail_spec {α : Type} {e : Error} {Q} (hQ : (Q.2.1 e).down) :
  ⦃ ⌜ True ⌝ ⦄ (Result.fail e : Result α) ⦃ Q ⦄ := by simpa [Triple]

/-- Extract a concrete `= .ok v` equation from a `noThrow` Triple.

Since `⇓ r => …` is `PostCond.noThrow` (its `fail`/`div` branches are
`False`), a Triple `⦃⌜True⌝⦄ x ⦃⇓ r => ⌜r = v⌝⦄` forces `x` onto the `ok`
branch with value `v`. This is the bridge that lets a pure-closure `[spec]`
hypothesis (stated as a Triple) be used as a plain Lean equation. -/
theorem result_eq_of_triple {α : Type} {x : Result α} {v : α}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄) : x = .ok v := by
  cases x <;> simp_all [Triple, WP.wp, PredTrans.apply]

/-- Converse of `result_eq_of_triple`: a `= .ok v` equation gives a `noThrow`
Triple. Lets a pure-equation hypothesis be fed to an `mvcgen`/Triple-based
spec. -/
theorem triple_of_result_eq {α : Type} {x : Result α} {v : α}
    (h : x = .ok v) : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄ := by
  subst h; exact Result.ok_spec (by simp)

/-- Read a `noThrow` postcondition off at a concrete `ok` value: a Triple
`⦃⌜True⌝⦄ x ⦃⇓ r => ⌜P r⌝⦄` together with `x = .ok v` yields `P v`. -/
theorem triple_ok_elim {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) (hx : x = .ok v) : P v := by
  subst hx; simpa [Triple, WP.wp, PredTrans.apply] using h

/-- Build a `noThrow` Triple from a concrete `ok` result and a fact about it. -/
theorem triple_ok_intro {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hv : P v) : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; exact Result.ok_spec hv

/-- A `noThrow` Triple forces `x` onto the `ok` branch, exposing both the value
and the postcondition. -/
theorem exists_ok_of_triple {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ a, x = .ok a ∧ P a := by
  cases hx : x with
  | ok a => exact ⟨a, rfl, triple_ok_elim h hx⟩
  | fail e => rw [hx] at h; simp_all [Triple, WP.wp, PredTrans.apply]
  | div => rw [hx] at h; simp_all [Triple, WP.wp, PredTrans.apply]

/-- Strengthen a `noThrow` Triple so the result's *value* survives `mvcgen`:
alongside the postcondition `P`, the result `r` is pinned by a self-referential
Triple stating that re-running `x` yields `r` again. This lets a spec whose
postcondition only mentions a projection of `r` (e.g. `r.2`) still expose the
full value after symbolic execution. -/
theorem triple_with_self {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ∧ ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r' => ⌜ r' = r ⌝ ⦄ ⌝ ⦄ := by
  obtain ⟨a, hx, hPa⟩ := exists_ok_of_triple h
  exact triple_ok_intro hx ⟨hPa, triple_of_result_eq hx⟩

theorem triple_in_hypothesis {f : Result α} {Q : α → Assertion _} (p : Prop)
    (h : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄)
    (hp : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => Q r → ⌜ p ⌝ ⦄) :
    p := by sorry

attribute [spec] Function.uncurry lift massert

@[spec]
theorem loop_spec
  {α β γ : Type}
  {P : PostCond β (PostShape.except Error (PostShape.except PUnit.{1} PostShape.pure))}
  (body : α → Result (ControlFlow α β)) (init : α)
  (inv : α → Prop)
  (rel : γ → γ → Prop)
  (termination : α → γ)
  (hwf : WellFounded rel)
  (h_inv_init : inv init)
  (h_body : ∀ x, inv x → ⦃ ⌜ True ⌝ ⦄ body x ⦃ post⟨
    fun cf => match cf with
      | .cont r => ⌜ inv r ∧ (rel (termination r) (termination x) ∨ (P.2.2.1 ()).down) ⌝
      | .done r => P.1 r,
    P.2.1, P.2.2.1⟩ ⦄) :
  ⦃ ⌜ True ⌝ ⦄ loop body init ⦃ P ⦄ := by
  suffices h : ∀ x, inv x → (wp⟦loop body x⟧ P).down by
    unfold Triple
    intro _
    exact h init h_inv_init
  by_cases hdiv : (P.2.2.1 ()).down
  · -- Divergence permitted: use partial-fixpoint induction.
    intro x hinv
    delta loop
    refine Lean.Order.fix_induct (loop._proof_1 body)
      (motive := fun g => ∀ x, inv x → (wp⟦g x⟧ P).down) ?_ ?_ x hinv
    · apply Lean.Order.admissible_pi
      intro y
      apply Lean.Order.admissible_pi
      intro _
      apply Lean.Order.admissible_apply (β := fun _ => Result β)
        (P := fun y r => (wp⟦r⟧ P).down) y
      exact Lean.Order.admissible_flatOrder _ hdiv
    · intro g IH y hinvy
      have hb : (wp⟦body y⟧ _).down := h_body y hinvy trivial
      cases hbe : body y with
      | ok cf =>
        rw [hbe] at hb
        cases cf with
        | cont r => exact IH r hb.1
        | done r => exact hb
      | fail e => rw [hbe] at hb; exact hb
      | div => rw [hbe] at hb; exact hb
  · -- Termination via WF induction on `rel`.
    intro x hinv
    induction hg : termination x using hwf.induction generalizing x
    rename_i g IH
    have hb : (wp⟦body x⟧ _).down := h_body x hinv trivial
    rw [loop.eq_1]
    cases hbe : body x with
    | ok cf =>
      rw [hbe] at hb
      cases cf with
      | cont r =>
        obtain ⟨hinvr, hrel | hd⟩ := hb
        · subst hg
          exact IH (termination r) hrel r hinvr rfl
        · exact absurd hd hdiv
      | done r => exact hb
    | fail e => rw [hbe] at hb; exact hb
    | div => rw [hbe] at hb; exact hb

open ScalarElab

iscalar_no_isize @[spec] theorem  «%S».hShiftRight_I8_spec (a : «%S») (b : I8) (hmin : b.val ≥ 0) (hmax : b.val < %Size) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃ ⇓ r => ⌜ r.val = a.val / (2 ^ b.val.toNat) ⌝ ⦄ := by
  mvcgen [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight]
    <;> grind [IScalar.val, Int.shiftRight_eq_div_pow]

iscalar_no_isize @[spec] theorem  «%S».hShiftRight_I16_spec (a : «%S») (b : I16) (hmin : b.val ≥ 0) (hmax : b.val < %Size) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃ ⇓ r => ⌜ r.val = a.val / (2 ^ b.val.toNat) ⌝ ⦄ := by
  mvcgen [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight]
    <;> grind [IScalar.val, Int.shiftRight_eq_div_pow]

iscalar_no_isize @[spec] theorem  «%S».hShiftRight_I32_spec (a : «%S») (b : I32) (hmin : b.val ≥ 0) (hmax : b.val < %Size) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃ ⇓ r => ⌜ r.val = a.val / (2 ^ b.val.toNat) ⌝ ⦄ := by
  mvcgen [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight]
    <;> grind [IScalar.val, Int.shiftRight_eq_div_pow]

iscalar_no_isize @[spec] theorem  «%S».hShiftRight_I64_spec (a : «%S») (b : I64) (hmin : b.val ≥ 0) (hmax : b.val < %Size) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃ ⇓ r => ⌜ r.val = a.val / (2 ^ b.val.toNat) ⌝ ⦄ := by
  mvcgen [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight]
    <;> grind [IScalar.val, Int.shiftRight_eq_div_pow]

iscalar_no_isize @[spec] theorem  «%S».hShiftRight_I128_spec (a : «%S») (b : I128) (hmin : b.val ≥ 0) (hmax : b.val < %Size) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃ ⇓ r => ⌜ r.val = a.val / (2 ^ b.val.toNat) ⌝ ⦄ := by
  mvcgen [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight]
    <;> grind [IScalar.val, Int.shiftRight_eq_div_pow]

end Aeneas.Std
