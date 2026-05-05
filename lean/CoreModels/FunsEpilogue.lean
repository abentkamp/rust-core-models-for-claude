import CoreModels.Alloc.Funs

namespace core_models

/-! ## core::iter::range — Range iteration

Aeneas extracts `for i in lo..hi { … }` to a loop driven by
`core.iter.range.IteratorRange.next`, which in turn uses a
`core.iter.range.Step` dictionary. We provide both, plus a `StepUsize`
instance, so that downstream extracted code that iterates over `Range<usize>`
type-checks. -/

namespace iter.step

/-- The `Iterator::next` implementation for `core::ops::range::Range<A>`,
    parameterised over the `Step` dictionary. -/
def IteratorRange.next {A : Type} (StepInst : Step A) :
    ops.range.Range A → Aeneas.Std.Result ((Option A) × ops.range.Range A) := fun range => do
  let cmp ← StepInst.cmpPartialOrdInst.partial_cmp range.start range.«end»
  let isLess : Bool := match cmp with
    | Option.some o => match o with
                       | core_models.cmp.Ordering.Less => true
                       | _ => false
    | _ => false
  if isLess then
    let cur ← StepInst.cloneCloneInst.clone range.start
    let next? ← StepInst.forward_checked cur 1#usize
    match next? with
    | Option.none      => .fail .panic
    | Option.some next => .ok (Option.some cur, { range with start := next })
  else .ok (Option.none, range)

end iter.step

abbrev ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next :=
  @iter.step.IteratorRange.next

end core_models

namespace alloc

/-! ## `[T]::to_vec` and `Box<[T]>::into_vec`

Aeneas's builtin name map turns `<[T]>::to_vec` into a reference to
`alloc.slice.Slice.to_vec` (and similarly for `into_vec`). Our local
`alloc/` crate provides those bodies, but under the `alloc.slice.Dummy`
namespace because of the standard "you can't `impl` for a foreign slice
type" workaround. Re-export them at the std-map name so downstream
extractions land on a defined symbol.
-/

noncomputable section

@[rust_fun "alloc::slice::{[@T]}::to_vec"]
def slice.Slice.to_vec
  {T : Type} (cloneInst : core_models.clone.Clone T) (s : Aeneas.Std.Slice T) :
  Aeneas.Std.Result (vec.Vec T alloc.Global) :=
  slice.Dummy.to_vec cloneInst s

@[rust_fun "alloc::slice::{alloc::boxed::Box<[@T], @A>}::into_vec"]
def slice.Slice.into_vec
  {T : Type} (A : Type) (s : Aeneas.Std.Slice T) : Aeneas.Std.Result (vec.Vec T A) :=
  slice.Dummy.into_vec A s

end

def vec.Vec.new := @vec.VecTGlobal.new
def vec.Vec.with_capacity := @vec.VecTGlobal.with_capacity

end alloc
