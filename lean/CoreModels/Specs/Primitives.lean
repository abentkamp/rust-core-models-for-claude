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
  (h_inv_cont : ∀ x Q,
    inv x →
    (∀ r, inv r → (Q.1 (.cont r)).down) →
    (P.2 ⊢ₑ Q.2) →
    ⦃ ⌜ True ⌝ ⦄ body x ⦃ Q ⦄)
  (h_inv_break : ∀ x Q,
    inv x →
    (∀ r, (P.1 r).down → (Q.1 (.done r)).down) →
    (P.2 ⊢ₑ Q.2) →
    ⦃ ⌜ True ⌝ ⦄ body x ⦃ Q ⦄)
  (h_div : (P.2.2.1 ()).down ∨ ∀ x Q, inv x →
    (∀ e, P.2.1 e ⊢ₛ Q.2.1 e) →
    (∀ y, rel (termination x) (termination y) → (Q.1 (.cont y)).down) →
    ⦃ ⌜ True ⌝ ⦄ body x ⦃ Q ⦄) :
  ⦃ ⌜ True ⌝ ⦄ loop body init ⦃ P ⦄ := by sorry
