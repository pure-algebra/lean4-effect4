import Effect4.Program.Ty
import Effect4.Program.AtomInventory

/-!
# Native atom typing (DI-40)

The typing half of the native atom inventory: `constGeneric`, `mono`, `projectProduct`, `typeOf`
and its monomorphic reading, and the table's own well-formedness (`atomWellFormed`,
`atom_table_wf`). The alphabet itself (`NativeAtom`, its name, arity, lookup and `eval`) is
`Machine/Term.lean`, below the stores, since L1 of the language push; the inventory `all` and
its projections are generated from that inductive's constructor list into
`Program/AtomInventory.lean`. The universal `all_complete` statement there forces an appended
constructor into the inventory, and every dispatch here covers the enum explicitly, so a new
constructor cannot inherit a fallback.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- The two input families advertised by the cause query atoms. -/
def causeInputError? : Ty → Option Ty
  | .causeOf error | .exitOf _ error => some error
  | _ => none

namespace NativeAtom

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

/-! ## The table's own well-formedness (the tooling plan 2.1)

Four structural obligations, decided once over the whole inventory rather than argued per
atom. They are the invariants a reader of the table may assume and an appended atom must
satisfy; what they are *not* is the semantic obligation (`typeOf` answers a type the atom's
`eval` inhabits), which quantifies over all `Ty` and all `Val` and is therefore not decidable
at all — that one is `NativeAtom.Sound` in `Laws/Program/Typed.lean`. -/

/-- Every structural obligation on one atom, as a Boolean over the table's own columns:

* the atom's name occurs exactly once in the inventory, so `ofName?` cannot be ambiguous;
* the arity agrees with the monomorphic signature's parameter count;
* `typeOf` at the declared signature answers the declared answer, so `mono` is metadata about
  `typeOf` rather than a second, drifting, typing rule;
* a const-generic atom has no monomorphic signature (DI-55: the literal rule only has content
  where a parameter is polymorphic). -/
def atomWellFormed (a : NativeAtom) : Bool :=
  (names.count a.name == 1)
    && (match a.mono, a.arity with
        | some (args, _), some n => args.length == n
        | some _, none => false
        | none, _ => true)
    && (match a.mono with
        | some (args, answer) => a.typeOf args == some answer
        | none => true)
    && (!a.constGeneric || a.mono.isNone)

/-- The whole table is well-formed. Decided in the kernel: `atomWellFormed` compares `String`s,
whose `DecidableEq` goes through `List Char`, and the elaborator's whnf expands a string
literal per character (`Lean/Meta/WHNF.lean`), so the reduction belongs where it is cheapest. -/
theorem atom_table_wf : NativeAtom.all.all atomWellFormed = true := by decide +kernel

end NativeAtom
end Effect4.Program
