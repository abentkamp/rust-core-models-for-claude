import Aeneas

open Aeneas Std WP Std.Do Result

theorem loop_spec
  {α β γ : Type}
  {P : PostCond β (PostShape.except Error (PostShape.except PUnit.{1} PostShape.pure))}
  (body : α → Result (ControlFlow α β)) (init : α)
  (inv : α → Prop)
  (rel : γ → γ → Prop)
  (termination : α → γ)
  (hwf : WellFounded rel)
  (h_inv_init : inv init)
  (h_inv_body : ∀ x Q,
    inv x →
    (∀ r, inv r → (Q.1 (.cont r)).down) →
    (∀ r, (P.1 r).down → (Q.1 (.done r)).down) →
    (P.2 ⊢ₑ Q.2) →
    ⦃ ⌜ True ⌝ ⦄ body x ⦃ Q ⦄)
  (h_div : (P.2.2.1 ()).down ∨ ∀ x Q, inv x →
    (∀ e, P.2.1 e ⊢ₛ Q.2.1 e) →
    (∀ y, rel (termination y) (termination x) → (Q.1 (.cont y)).down) →
    ⦃ ⌜ True ⌝ ⦄ body x ⦃ Q ⦄) :
  ⦃ ⌜ True ⌝ ⦄ loop body init ⦃ P ⦄ := by
  suffices h : ∀ x, inv x → (wp⟦loop body x⟧ P).down by
    unfold Triple
    intro _
    exact h init h_inv_init
  cases h_div with
  | inl hdiv =>
    -- Divergence permitted: use partial-fixpoint induction.
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
      let Q : PostCond (ControlFlow α β)
          (PostShape.except Error (PostShape.except PUnit.{1} PostShape.pure)) :=
        ⟨fun cf => match cf with
           | .cont r => ⌜(wp⟦g r⟧ P).down⌝
           | .done r => P.1 r,
         P.2⟩
      have hbody : ⦃ ⌜True⌝ ⦄ body y ⦃ Q ⦄ := by
        apply h_inv_body y Q hinvy
        · intro r hir; exact IH r hir
        · intro r hpr; exact hpr
        · exact (PostCond.entails.refl _).2
      have hb : (wp⟦body y⟧ Q).down := hbody trivial
      simp only [Result.instWP] at hb ⊢
      cases hbe : body y with
      | ok cf =>
        rw [hbe] at hb
        cases cf with
        | cont r => simp only [Q] at hb; exact hb
        | done r => simp only [Q] at hb; exact hb
      | fail e => rw [hbe] at hb; simp only [Q] at hb; exact hb
      | div => rw [hbe] at hb; simp only [Q] at hb; exact hb
  | inr hterm =>
    -- Termination via WF induction on `rel (termination x)`.
    intro x hinv
    induction hg : termination x using hwf.induction generalizing x
    rename_i g IH
    let Q1 : PostCond (ControlFlow α β)
        (PostShape.except Error (PostShape.except PUnit.{1} PostShape.pure)) :=
      ⟨fun cf => match cf with
         | .cont r => ⌜inv r⌝
         | .done r => P.1 r,
       P.2⟩
    let Q2 : PostCond (ControlFlow α β)
        (PostShape.except Error (PostShape.except PUnit.{1} PostShape.pure)) :=
      ⟨fun cf => match cf with
         | .cont r => ⌜rel (termination r) (termination x)⌝
         | .done _ => ⌜True⌝,
       P.2⟩
    have hb_inv : ⦃ ⌜True⌝ ⦄ body x ⦃ Q1 ⦄ := by
      apply h_inv_body x Q1 hinv
      · intro r hir; exact hir
      · intro r hpr; exact hpr
      · exact (PostCond.entails.refl _).2
    have hb_term : ⦃ ⌜True⌝ ⦄ body x ⦃ Q2 ⦄ := by
      apply hterm x Q2 hinv
      · intro _; exact SPred.entails.refl _
      · intro y hr; exact hr
    have hbi : (wp⟦body x⟧ Q1).down := hb_inv trivial
    have hbt : (wp⟦body x⟧ Q2).down := hb_term trivial
    rw [loop.eq_1]
    simp only [Result.instWP] at hbi hbt ⊢
    cases hbe : body x with
    | ok cf =>
      rw [hbe] at hbi hbt
      cases cf with
      | cont r =>
        simp only [Q1, Q2] at hbi hbt
        subst hg
        exact IH (termination r) hbt r hbi rfl
      | done r => simp only [Q1] at hbi; exact hbi
    | fail e => rw [hbe] at hbi; simp only [Q1] at hbi; exact hbi
    | div => rw [hbe] at hbi; simp only [Q1] at hbi; exact hbi
