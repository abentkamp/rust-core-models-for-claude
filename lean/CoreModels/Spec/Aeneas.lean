import CoreModels.Funs

namespace Aeneas.Std
open Std.Do WP Std.Do Result

set_option mvcgen.warning false

@[spec]
theorem Result.ok_spec {α : Type} {a : α} {Q} (hQ : (Q.1 a).down) :
  ⦃ ⌜ True ⌝ ⦄ Result.ok a ⦃ Q ⦄ := by simpa [Triple]

@[spec]
theorem Result.fail_spec {α : Type} {e : Error} {Q} (hQ : (Q.2.1 e).down) :
  ⦃ ⌜ True ⌝ ⦄ (Result.fail e : Result α) ⦃ Q ⦄ := by simpa [Triple]

attribute [spec] Function.uncurry lift

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
      simp only [Result.instWP] at hb ⊢
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
    simp only [Result.instWP] at hb ⊢
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

end Aeneas.Std
