import Aeneas

open Aeneas.Std

namespace CoreModels.core

/-! ## Function closures -/

namespace ops.function
structure FnOnce (Self : Type) (Args : Type) (Self_Output : Type) where
  call_once : Self → Args → Result Self_Output

structure FnMut (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnOnceInst : FnOnce Self Args Self_Clause0_Output
  call_mut : Self → Args → Result (Self_Clause0_Output × Self)

structure Fn (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnMutInst : FnMut Self Args Self_Clause0_Output
  call : Self → Args → Result Self_Clause0_Output
end ops.function

/-! ## Phantom — used by `Aeneas/Alloc/Types.lean` rewrite

`vec.Vec T A` in core-models is `Seq T × PhantomData<A>`. We can't reuse
the existing `core.marker.PhantomData T := T` for the alloc rewrite (the
extracted constructor sites use `()`, which is `Unit`). We instead rewrite
the `core.marker.PhantomData A` field type to `core.Phantom A`.

`Phantom` is a *non-reducible* `structure` with a phantom type parameter:
the parameter must appear syntactically in the type for generic-allocator
type inference to keep working at call sites (`alloc.vec.Vec.clear` etc.
take the `A` implicit). A `@[reducible] def Phantom _ := Unit` would
defeat that. -/

structure Phantom (A : Type) where mk ::
deriving Inhabited

/-! ## Option

Rust's `Option` aliased to Lean's built-in

-/

namespace option

abbrev Option := _root_.Option
@[match_pattern] abbrev Option.Some {T} (x : T) : Option T := _root_.Option.some x
@[match_pattern] abbrev Option.None {T} : Option T := _root_.Option.none

end option

inductive cmp.Ordering where
| Less : cmp.Ordering
| Equal : cmp.Ordering
| Greater : cmp.Ordering

end CoreModels.core

namespace CoreModels

/-! ## Rust's `Result` enum -/

namespace core.result

inductive Result (T : Type) (E : Type) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E

def Result.ok {T E : Type} (r : Result T E) : Aeneas.Std.Result (_root_.Option T) :=
  match r with
  | Result.Ok t  => Aeneas.Std.Result.ok (some t)
  | Result.Err _ => Aeneas.Std.Result.ok none

/-- `Result<T, E>::err(self) -> Option<E>`. Same `abbrev` rationale. -/
def Result.err {T E : Type} (r : Result T E) : Aeneas.Std.Result (_root_.Option E) :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok none
  | Result.Err e => Aeneas.Std.Result.ok (some e)

/-- `Result<T, E>::is_ok(&self) -> bool`. -/
def Result.is_ok {T E : Type} (r : Result T E) : Aeneas.Std.Result Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok true
  | Result.Err _ => Aeneas.Std.Result.ok false

/-- `Result<T, E>::is_err(&self) -> bool`. -/
def Result.is_err {T E : Type} (r : Result T E) : Aeneas.Std.Result Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok false
  | Result.Err _ => Aeneas.Std.Result.ok true
end core.result


/-! ## Hax lib -/
namespace hax_lib

@[reducible] def int.Int := _root_.Int

end hax_lib

export Aeneas.Std (
  core.clone.Clone core.marker.Copy
)

end CoreModels
