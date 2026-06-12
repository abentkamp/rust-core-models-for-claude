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

The induction is expressed as a recursion of the lemma on the tail: the `have
ih` is a recursive call providing the worker's spec for `t`, which `mvcgen`
then picks up for the recursive `array_from_fn_go` call in the body. -/
private theorem array_from_fn_go_pure
    {T F : Type}
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T) (l : List Nat)
    (hpure : ∀ k ∈ l,
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn_go inst c l
    ⦃ ⇓ r => ⌜ r = l.map f ⌝ ⦄ := by
  match l with
  | [] =>
    unfold rust_primitives.slice.array_from_fn_go
    mvcgen
  | h :: t =>
    -- IH stated parametrically over the (preserved) closure state, so `mvcgen`
    -- can unify it against the recursive call `array_from_fn_go inst p.2 t`
    -- (where `p.2 = c`), emitting the `c' = c` side condition for `grind`.
    have ih : ∀ c' : F, c' = c →
        ⦃ ⌜ True ⌝ ⦄
        rust_primitives.slice.array_from_fn_go inst c' t
        ⦃ ⇓ r => ⌜ r = t.map f ⌝ ⦄ := by
      intro c' hc'; subst c'
      exact array_from_fn_go_pure inst c f t (fun k hk => hpure k (List.mem_cons_of_mem _ hk))
    have hh := hpure h List.mem_cons_self
    unfold rust_primitives.slice.array_from_fn_go
    mvcgen [hh, ih] <;> simp_all [List.map_cons]

/-- Lean-level equation for `array_from_fn` over a pure closure: the result is
    the array whose `i`-th cell is `f i`. -/
theorem array_from_fn_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    rust_primitives.slice.array_from_fn N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hgo : rust_primitives.slice.array_from_fn_go inst c (List.range N.val)
      = .ok ((List.range N.val).map f) :=
    result_eq_of_triple <|
      array_from_fn_go_pure inst c f (List.range N.val)
        (fun k hk => triple_of_result_eq (hpure k (List.mem_range.mp hk)))
  unfold CoreModels.rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [hgo] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [hgo] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [hgo] at heq
    have hres : result = (List.range N.val).map f := (Result.ok.inj heq).symm
    subst hres
    rfl

end CoreModels
