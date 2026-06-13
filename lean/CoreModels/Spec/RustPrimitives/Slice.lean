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

/-- The result array's underlying list is `(List.range N).map f`, for the
    pure closure realizing `f`. The `f`-indexed form, for callers that need the
    exact resulting array (e.g. `core.convert`'s slice→array `try_from`). -/
theorem array_from_fn_eq
    {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hf : ∀ k : Nat, k < N.val → inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn N inst c
    ⦃ ⇓ a => ⌜ a = ⟨(List.range N.val).map f,
                   by simp [List.length_map, List.length_range]⟩ ⌝ ⦄ := by
  have hgo := array_from_fn_go_pure inst c f (List.range N.val)
    (fun k hk => triple_of_result_eq (hf k (List.mem_range.mp hk)))
  unfold rust_primitives.slice.array_from_fn
  mvcgen [hgo] <;> simp_all [List.length_map, List.length_range]

/-- **Triple spec for `array_from_fn` over a pure closure.**

`f`-free, so it can be `@[spec]` (nothing for `mvcgen` to leave as a
metavariable): assuming each `call_mut` preserves the state (`hpure`), the
result array's `i`-th cell is exactly the value `call_mut c i` produces —
stated as a Triple in the postcondition. A caller who knows what `call_mut`
returns recovers the cell via `triple_ok_elim`. -/
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
  have hex : ∀ k, k < N.val → ∃ v : T, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (v, c) := by
    intro k hk
    obtain ⟨⟨v, st⟩, hok, hst⟩ := exists_ok_of_triple (hpure k hk)
    have : st = c := hst
    exact ⟨v, this ▸ hok⟩
  classical
  let f : Nat → T := fun k => if h : k < N.val then (hex k h).choose else default
  have hf : ∀ k : Nat, k < N.val → inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk
    show inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok ((dite _ (fun h => (hex k h).choose) _), c)
    rw [dif_pos hk]
    exact (hex k hk).choose_spec
  have hspec := array_from_fn_eq N inst c f hf
  mvcgen [hspec]
  rintro rfl i hi
  apply triple_ok_intro (hf i hi)
  show f i = ((List.range N.val).map f)[i]!
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

end CoreModels
