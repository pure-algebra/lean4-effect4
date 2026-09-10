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
  deriving DecidableEq, BEq

namespace NativeAtom

/-- Declaration order is the existing generated profile order. -/
def all : List NativeAtom :=
  [.succ, .pred, .isZero, .boolNot, .add, .lt, .eq, .pair, .fst, .snd, .strings,
   .causeIsFail, .causeError, .causeIsDie, .causeIsInterrupt, .boolOr, .boolAnd]

theorem all_complete (atom : NativeAtom) : atom ∈ all := by
  cases atom <;> simp [all]

def name : NativeAtom → String
  | .succ => "succ" | .pred => "pred" | .isZero => "isZero" | .boolNot => "not"
  | .add => "add" | .lt => "lt" | .eq => "eq" | .pair => "pair"
  | .fst => "fst" | .snd => "snd" | .strings => "strings"
  | .causeIsFail => "causeIsFail" | .causeError => "causeError"
  | .causeIsDie => "causeIsDie" | .causeIsInterrupt => "causeIsInterrupt"
  | .boolOr => "or" | .boolAnd => "and"

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
  | .causeIsFail | .causeError | .causeIsDie | .causeIsInterrupt => some 1
  | .add | .lt | .eq | .pair | .boolOr | .boolAnd => some 2
  | .strings => none

/-- Schemes are explicit none; generators must supply and check their target arms. -/
def mono : NativeAtom → Option (List Ty × Ty)
  | .succ | .pred => some ([.nat], .nat)
  | .isZero => some ([.nat], .bool)
  | .boolNot => some ([.bool], .bool)
  | .add => some ([.nat, .nat], .nat)
  | .lt => some ([.nat, .nat], .bool)
  | .boolOr | .boolAnd => some ([.bool, .bool], .bool)
  | .eq | .pair | .fst | .snd | .strings
  | .causeIsFail | .causeError | .causeIsDie | .causeIsInterrupt => none

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
  | .succ, _ | .pred, _ | .isZero, _ | .boolNot, _ | .add, _ | .lt, _ | .eq, _
  | .pair, _ | .fst, _ | .snd, _
  | .causeIsFail, _ | .causeError, _ | .causeIsDie, _ | .causeIsInterrupt, _
  | .boolOr, _ | .boolAnd, _ => none

def typeOf : NativeAtom → List Ty → Option Ty
  | .succ, [.nat] => some .nat
  | .pred, [.nat] => some .nat
  | .isZero, [.nat] => some .bool
  | .boolNot, [.bool] => some .bool
  | .add, [.nat, .nat] => some .nat
  | .lt, [.nat, .nat] => some .bool
  | .eq, [.nat, .nat] => some .bool
  | .eq, [.string, .string] => some .bool
  | .pair, [a, b] => some (.prod a b)
  | .fst, [.prod a _] => some a
  | .snd, [.prod _ b] => some b
  | .strings, tys => if tys.all (· == .string) then some (.list .string) else none
  | .causeIsFail, [input] | .causeIsDie, [input] | .causeIsInterrupt, [input] =>
      (causeInputError? input).map fun _ => .bool
  | .causeError, [input] => (causeInputError? input).map Ty.option
  | .boolOr, [.bool, .bool] | .boolAnd, [.bool, .bool] => some .bool
  | .succ, _ | .pred, _ | .isZero, _ | .boolNot, _ | .add, _ | .lt, _ | .eq, _
  | .pair, _ | .fst, _ | .snd, _
  | .causeIsFail, _ | .causeError, _ | .causeIsDie, _ | .causeIsInterrupt, _
  | .boolOr, _ | .boolAnd, _ => none

end NativeAtom
end Effect4.Program
