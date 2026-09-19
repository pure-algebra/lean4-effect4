import Effect4.Program.Ty
import Effect4.Machine.Term

/-!
# Native atom typing (DI-40)

The typing half of the native atom inventory: `constGeneric`, `mono`, `projectProduct`, `typeOf`
and its monomorphic reading. The inventory itself (`NativeAtom`, its names, arity and `eval`)
is `Machine/Term.lean`, below the stores, since L1 of the language push. The universal
`all_complete` statement there forces an appended constructor into the inventory, and every
dispatch here covers the enum explicitly, so a new constructor cannot inherit a fallback.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- The two input families advertised by the cause query atoms. -/
def causeInputError? : Ty → Option Ty
  | .causeOf error | .exitOf _ error => some error
  | _ => none

namespace NativeAtom

/-- Whether the atom's parameters are const-generic (DI-55, the prelude's
`pair<const A, const B>`): a string literal argument keeps its literal type under the literal
rule (`litArgTy`, DI-15). Only `pair` is; every other atom widens a literal to `string`, as
TypeScript does at a non-`const` parameter. -/
def constGeneric : NativeAtom → Bool
  | .pair => true
  | .succ | .pred | .isZero | .boolNot | .add | .lt | .eq | .fst | .snd | .strings
  | .causeIsFail | .causeError | .causeIsDie | .causeIsInterrupt | .boolOr | .boolAnd
  | .tagIs | .isSome | .getOrElse => false

/-- Monomorphic metadata for generated interfaces. Polymorphic schemes are `none`;
`typeOf` remains their single executable typing owner. -/
def mono : NativeAtom → Option (List Ty × Ty)
  | .succ | .pred => some ([.nat], .nat)
  | .isZero => some ([.nat], .bool)
  | .boolNot => some ([.bool], .bool)
  | .add => some ([.nat, .nat], .nat)
  | .lt => some ([.nat, .nat], .bool)
  | .boolOr | .boolAnd => some ([.bool, .bool], .bool)
  | .eq | .pair | .fst | .snd | .strings
  | .causeIsFail | .causeError | .causeIsDie | .causeIsInterrupt | .tagIs
  | .isSome | .getOrElse => none

/-- The selected column of a product or a union of products. `second = false` selects
the first column. Bottom contributes no value; every other non-product alternative
refuses, including lists whose values may happen to have two elements. Direct products
retain their existing component type, and unions use the shared canonical join. -/
def projectProduct (second : Bool) : Ty → Option Ty
  | .prod a b => some (if second then b else a)
  | .union a b => do
    let left ← projectProduct second a
    let right ← projectProduct second b
    some (Ty.join left right)
  | .never => some .never
  | _ => none

/-- The typing of an application by its argument types (DI-40; DI-15, the 2026-09-12 clause).
A fixed-signature atom accepts each argument at a subtype of its parameter (`Ty.sub`:
TypeScript assignability at a call site), so `succ` takes a `nat` and therefore a `never`,
and `eq` takes two naturals or two strings and therefore two string literals — which is what
`eq (fst (pair "A" m)) "A"` needs once `pair`'s literal arguments type at their literals.
`pair` is polymorphic and answers the product of exactly the types it is given; `fst`/`snd`
project products and join the selected columns of product unions; `strings` takes any
number of string-typed arguments; the cause queries
take a `causeOf`/`exitOf` and are unchanged. `isSome` accepts an option;
`getOrElse` keeps its payload type and checks the default by canonical subsumption.
Both are eager pure applications; they introduce no branch refinement. -/
def typeOf : NativeAtom → List Ty → Option Ty
  | .succ, [a] => if a.sub .nat then some .nat else none
  | .pred, [a] => if a.sub .nat then some .nat else none
  | .isZero, [a] => if a.sub .nat then some .bool else none
  | .boolNot, [a] => if a.sub .bool then some .bool else none
  | .add, [a, b] => if a.sub .nat && b.sub .nat then some .nat else none
  | .lt, [a, b] => if a.sub .nat && b.sub .nat then some .bool else none
  | .eq, [a, b] =>
    if (a.sub .nat && b.sub .nat) || (a.sub .string && b.sub .string) then some .bool else none
  | .pair, [a, b] => some (.prod a b)
  | .fst, [a] => projectProduct false a
  | .snd, [a] => projectProduct true a
  | .strings, tys => if tys.all (·.sub .string) then some (.list .string) else none
  | .causeIsFail, [input] | .causeIsDie, [input] | .causeIsInterrupt, [input] =>
      (causeInputError? input).map fun _ => .bool
  | .causeError, [input] => (causeInputError? input).map Ty.option
  | .boolOr, [a, b] | .boolAnd, [a, b] => if a.sub .bool && b.sub .bool then some .bool else none
  -- the tag is a string (a literal is one); the tested value is anything (`unknown` on the host)
  | .tagIs, [t, _] => if t.sub .string then some .bool else none
  | .isSome, [.option _] => some .bool
  | .getOrElse, [.option a, b] => if b.normalize.sub a.normalize then some a else none
  | .succ, _ | .pred, _ | .isZero, _ | .boolNot, _ | .add, _ | .lt, _ | .eq, _
  | .pair, _ | .fst, _ | .snd, _
  | .causeIsFail, _ | .causeError, _ | .causeIsDie, _ | .causeIsInterrupt, _
  | .boolOr, _ | .boolAnd, _ | .tagIs, _ | .isSome, _ | .getOrElse, _ => none

/-- A monomorphic row's typing is exactly argument-wise subsumption (`mono`, `typeOf`). -/
theorem typeOf_mono (atom : NativeAtom) (args answer : _) (h : atom.mono = some (args, answer))
    (tys : List Ty) :
    typeOf atom tys =
      if tys.length = args.length ∧ (tys.zip args).all (fun (a, e) => a.sub e) then some answer
      else none := by
  cases atom <;> simp only [mono, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals
    match tys with
    | [] => rfl
    | [_] => simp [typeOf]
    | [_, _] => simp [typeOf]
    | _ :: _ :: _ :: _ => rfl

end NativeAtom
end Effect4.Program
