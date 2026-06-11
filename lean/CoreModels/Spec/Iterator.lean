import CoreModels.Core.Funs
import CoreModels.Alloc.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

@[spec]
theorem IteratorRange_next_CoreIterRangeStep_spec (i e : Usize) {Q}
      (h_lt : (h : i.val < e.val) →
        ∀ (s : Usize), s.val = i.val + 1 → (Q.1 (some i, { start := s, «end» := e })).down)
      (h_ge : i.val ≥ e.val → (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
  simp only [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
    core.Usize.Insts.CoreCloneClone.clone, core.Usize.Insts.CoreIterRangeStep.forward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize]
  mvcgen [uncurry]
    <;> grind [UScalar.overflowing_add, BitVec.uaddOverflow, UScalar.overflowing_add_eq]
