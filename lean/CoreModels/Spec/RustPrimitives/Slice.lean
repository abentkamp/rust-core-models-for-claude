import CoreModels.Core.Funs
import CoreModels.Spec.Aeneas

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

/-! ## Generic pure-closure reasoning for `rust_primitives::slice::array_from_fn`.

`array_from_fn` builds an array by threading a `FnMut` closure across `0 .. N`
(via the recursive worker `array_from_fn_go`). When that closure is *pure* —
`call_mut c i = .ok (f i, c)` for some `f : Nat → T`, leaving the state `c`
untouched — the result is just `.ok (List.range N |>.map f)`. Both
`core.array.from_fn` (see `Spec/Core/Array.lean`) and the slice→array
`core.convert` `try_from` (see `Spec/Core/Convert.lean`) are instances of this
pattern, so the recursion lives here once. -/

/-- The recursive worker over a pure closure returns `l.map f`, as a Triple.

`induction l generalizing c` yields an induction hypothesis abstract over the
closure state `c` (and the tail), so `mvcgen` can pick it up directly as the
spec for the recursive `array_from_fn_go` call in the body — no explicit case
match, and no need to fix the state. `simp_all` (unfolding `Triple`) discharges
the head-element step and the IH's purity premise from `hpure`. -/
private theorem array_from_fn_go_pure
    {T F : Type}
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T) (l : List Nat)
    (hpure : ∀ k ∈ l,
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn_go inst c l
    ⦃ ⇓ r => ⌜ r = l.map f ⌝ ⦄ := by
  induction l generalizing c with
  | nil =>
    unfold rust_primitives.slice.array_from_fn_go
    mvcgen
  | cons h t ih =>
    have hh := hpure h List.mem_cons_self
    unfold rust_primitives.slice.array_from_fn_go
    mvcgen [hh, ih] <;> simp_all [List.map_cons, Triple, WP.wp, PredTrans.apply]

/-- **Triple spec for `array_from_fn` over a pure closure.** Proved by `mvcgen`
    stepping through the `do` block, with `array_from_fn_go_pure` supplying the
    worker spec: the result array's underlying list is `(List.range N).map f`. -/
@[spec]
theorem array_from_fn_spec
    {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn N inst c
    ⦃ ⇓ a => ⌜ a = ⟨(List.range N.val).map f,
                   by simp [List.length_map, List.length_range]⟩ ⌝ ⦄ := by
  have hgo := array_from_fn_go_pure inst c f (List.range N.val)
    (fun k hk => hpure k (List.mem_range.mp hk))
  unfold rust_primitives.slice.array_from_fn
  mvcgen [hgo] <;> simp_all [List.length_map, List.length_range]

end CoreModels
