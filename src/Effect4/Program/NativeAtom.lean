import Effect4.Program.Typing
import Effect4.Program.ErrorQueries
import Effect4.Machine.Stores

/-!
# Native atom inventory (DI-40)

One finite owner for native atom names, arities, typing and evaluation. Stored Term.app
continues to carry a String; this enum is an implementation inventory, not stored syntax.
The universal all_complete statement forces an appended constructor into the inventory.
Every dispatch covers the enum explicitly, so a new constructor cannot inherit a fallback.
Generators project names/signatures from this owner; their scheme code remains checked
target implementation. No host predicate or generated-code equivalence is asserted here.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- `strings` builds the native list-of-strings image, including the empty list. -/
def stringsAtom (vs : List Val) : Option Val :=
  if vs.all (fun | Val.str _ => true | _ => false) then some (Val.list vs) else none

inductive NativeAtom
  | succ | pred | isZero | boolNot | add | lt | eq | pair | fst | snd | strings
  | causeIsFail | causeError | causeIsDie | causeIsInterrupt | boolOr | boolAnd
  /-- The tag test (DI-39, part 4 commit 3, 2026-09-12): `tagIs(tag, e)` is true exactly on a
  pair whose first component is the string `tag` (`.list [.str tag, _]`, the pair
  representation of `Typed.lean`), and false on every other value — a bare string, a natural,
  a pair whose first component is not the tag — so it never refuses a well-typed program
  (an error typed `union (prod (lit "A") string) string` can be a bare string). It is what a
  `catchIf` test names for the tag residual (`Typing.lean` `catchIfError`, `Ty.diffTag`), and
  it prints as `tagIs("A", aN)` through the atom printer with `tagIs` in the prelude. Atoms
  are spelled by name on the wire, so appending it moves no ordinal and no byte. -/
  | tagIs
  /-- Pure option elimination; applications remain named terms on the wire (DI-78). -/
  | isSome | getOrElse
  deriving DecidableEq, BEq

namespace NativeAtom

/-- Declaration order is the existing generated profile order. -/
def all : List NativeAtom :=
  [.succ, .pred, .isZero, .boolNot, .add, .lt, .eq, .pair, .fst, .snd, .strings,
   .causeIsFail, .causeError, .causeIsDie, .causeIsInterrupt, .boolOr, .boolAnd, .tagIs, .isSome, .getOrElse]

theorem all_complete (atom : NativeAtom) : atom ∈ all := by
  cases atom <;> simp [all]

def name : NativeAtom → String
  | .succ => "succ" | .pred => "pred" | .isZero => "isZero" | .boolNot => "not"
  | .add => "add" | .lt => "lt" | .eq => "eq" | .pair => "pair"
  | .fst => "fst" | .snd => "snd" | .strings => "strings"
  | .causeIsFail => "causeIsFail" | .causeError => "causeError"
  | .causeIsDie => "causeIsDie" | .causeIsInterrupt => "causeIsInterrupt"
  | .boolOr => "or" | .boolAnd => "and"
  | .tagIs => "tagIs"
  | .isSome => "isSome" | .getOrElse => "getOrElse"

def names : List String := all.map name

/-- Exact lookup over the complete inventory; unknown names remain refused. -/
def ofName? (value : String) : Option NativeAtom := all.find? (fun atom => atom.name == value)

theorem ofName?_name (atom : NativeAtom) : ofName? atom.name = some atom := by
  cases atom <;> rfl

theorem ofName?_sound {value : String} {atom : NativeAtom}
    (h : ofName? value = some atom) : atom.name = value := by
  have found : (atom.name == value) = true :=
    List.find?_some (p := fun candidate : NativeAtom => candidate.name == value) h
  exact eq_of_beq found

theorem name_injective {a b : NativeAtom} (h : a.name = b.name) : a = b := by
  have ha := ofName?_name a
  rw [h, ofName?_name] at ha
  exact Option.some.inj ha.symm

/-- A consumer inventory must cover every constructor, not just its own supplied rows. -/
def covers (consumerNames : List String) : Bool := names.all consumerNames.contains

theorem covers_iff (consumerNames : List String) :
    covers consumerNames = true ↔ ∀ atom : NativeAtom, atom.name ∈ consumerNames := by
  simp only [covers, names, List.all_eq_true, List.mem_map, List.contains_iff_mem]
  constructor
  · intro h atom
    exact h atom.name ⟨atom, all_complete atom, rfl⟩
  · intro h value hv
    obtain ⟨atom, _, rfl⟩ := hv
    exact h atom

def arity : NativeAtom → Option Nat
  | .succ | .pred | .isZero | .boolNot | .fst | .snd
  | .causeIsFail | .causeError | .causeIsDie | .causeIsInterrupt | .isSome => some 1
  | .add | .lt | .eq | .pair | .boolOr | .boolAnd | .tagIs | .getOrElse => some 2
  | .strings => none

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

/-- The tag test on a value (DI-39): true exactly on a pair whose first component is the
tag; false on every other value. Total, so `tagIs` never answers `none` on a string tag. -/
def tagHit (tag : String) : Val → Bool
  | .list [.str t, _] => t == tag
  | _ => false

def eval : NativeAtom → List Val → Option Val
  | .succ, [Val.nat n] => some (Val.nat (n + 1))
  | .pred, [Val.nat n] => some (Val.nat (n - 1))
  | .isZero, [Val.nat n] => some (Val.bool (n = 0))
  | .boolNot, [Val.bool b] => some (Val.bool (!b))
  | .add, [Val.nat a, Val.nat b] => some (Val.nat (a + b))
  | .lt, [Val.nat a, Val.nat b] => some (Val.bool (decide (a < b)))
  | .eq, [Val.nat a, Val.nat b] => some (Val.bool (a = b))
  | .eq, [Val.str a, Val.str b] => some (Val.bool (a == b))
  | .pair, [a, b] => some (Val.list [a, b])
  | .fst, [.list (a :: _)] => some a
  | .snd, [.list (_ :: b :: _)] => some b
  | .strings, vs => stringsAtom vs
  | .causeIsFail, [value] => queryTag .fail value
  | .causeError, [value] => queryError value
  | .causeIsDie, [value] => queryTag .die value
  | .causeIsInterrupt, [value] => queryTag .interrupt value
  | .boolOr, [Val.bool a, Val.bool b] => some (Val.bool (a || b))
  | .boolAnd, [Val.bool a, Val.bool b] => some (Val.bool (a && b))
  | .tagIs, [Val.str tag, v] => some (Val.bool (tagHit tag v))
  | .isSome, [Store.Val.none] => some (Val.bool false)
  | .isSome, [Store.Val.some _] => some (Val.bool true)
  | .getOrElse, [Store.Val.none, fallback] => some fallback
  | .getOrElse, [Store.Val.some value, _] => some value
  | .succ, _ | .pred, _ | .isZero, _ | .boolNot, _ | .add, _ | .lt, _ | .eq, _
  | .pair, _ | .fst, _ | .snd, _
  | .causeIsFail, _ | .causeError, _ | .causeIsDie, _ | .causeIsInterrupt, _
  | .boolOr, _ | .boolAnd, _ | .tagIs, _ | .isSome, _ | .getOrElse, _ => none

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
