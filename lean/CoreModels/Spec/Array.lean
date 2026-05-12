import CoreModels.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels
open Aeneas Aeneas.Std Std.Do WP Std.Do Result

set_option mvcgen.warning false

open core_models ScalarElab

uscalar @[spec] theorem «%S».Core_modelsCmpPartialEqArray.eq_spec {N : Std.Usize} {Q}
  (a : Array «%S» N) (b : Array «%S» N) (h : (Q.1 (a.val == b.val)).down) :
  ⦃ ⌜ True ⌝ ⦄
  Array.Insts.Core_modelsCmpPartialEqArray.eq «%S».Insts.Core_modelsCmpPartialEq'S a b
  ⦃ Q ⦄ := by
  mvcgen -trivial [Array.Insts.Core_modelsCmpPartialEqArray.eq,
    Array.Insts.Core_modelsCmpPartialEqArray.eq_loop,
    Array.Insts.Core_modelsCmpPartialEqArray.eq_loop.body, rust_primitives.slice.array_index,
    «%S».Insts.Core_modelsCmpPartialEq'S]
  case vc1.γ => exact Nat
  case vc4.termination => exact fun i => N.val - i.val
  case vc3.rel => exact (· < ·)
  case vc5.hwf => exact wellFounded_lt
  case vc2.inv => exact fun i => a.val.take i.val = b.val.take i.val
  case vc10 =>
    constructor
    · simp_all [@List.take_add, @List.take_one, -List.take_append_getElem]
    · grind
  · grind
  · grind
  · grind
  · grind
  · convert h; grind
  · convert h; grind

end CoreModels
