import Effect4.Machine.Alphabets

/-!
# Machine.Term — the first-order term language and its evaluation, below the stores

The literals (`Lit`), the positional variables (`Var`), the terms (`Term`, `Terms`: a variable,
a literal, or an atom applied to terms), their scope check, the closed atom alphabet
(`NativeAtom`: its name, arity, lookup and `eval`) and the evaluator (`evalTerm`), together with the error
image (`errOf`, `valOfErr`) and the cause queries the query atoms read. Everything here is
first-order data over the shared carrier `Val` and needs no type: the atoms' *typing*
(`NativeAtom.typeOf`) is `Program/NativeAtom.lean`, the literals' types (`Lit.ty`) are
`Program/Eff.lean`. The module sits below `Machine/Stores.lean` so that a store step can
evaluate a term (the function-taking rows of decisions row 43 carry one) and stay one atomic
step. Namespace `Effect4.Program` is kept: the wire tags, the generator and every consumer
name these constants by it (L1 of the language push, `docs/research/2026-09-18-rows-42-43-plan.md` §2c).
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## The error image (DI-62) -/

/-- The represented error image: natural, text, and the two-string package payload.
Every other raw value collapses to `boom`; the supported-error typing guards exclude those
values at each admitted failure introduction (DI-62). -/
def errOf : Val → Err
  | .nat n => .tag n
  | .str s => .text s
  | .list [.str t, .str m] => .tagged t m
  | _ => .boom

/-- The partial inverse of `errOf`. `boom` has no typed payload; no arm invents one. -/
def valOfErr : Err → Option Val
  | .boom => none
  | .tag n => some (.nat n)
  | .tagged tag message => some (.list [.str tag, .str message])
  | .text s => some (.str s)

/-! ## Cause queries (DI-09) -/

/-- First Fail including boom. Conversion must happen after this search. -/
def firstFailure? (cause : CauseV) : Option Err :=
  cause.reasons.findSome? Reason.error?

/-- The error binder/query payload. A first boom stays none even if a later Fail converts. -/
def firstErrorValue? (cause : CauseV) : Option Val :=
  (firstFailure? cause).bind valOfErr

/-- Scalar cause/exit query input. Invalid raw values are refused, not flattened. -/
def queryReasons? : Val → Option (List (Reason Err Defect FiberId Ann))
  | Val.exitOk _ => some []
  | value => (Val.cause? value).map Cause.reasons

def queryTag (tag : ReasonTag) (value : Val) : Option Val :=
  (queryReasons? value).map fun reasons =>
    Val.bool (reasons.any fun reason => decide (reason.tag = tag))

/-- Cause.findErrorOption with DI-09's documented boom boundary. -/
def queryError (value : Val) : Option Val := do
  let reasons ← queryReasons? value
  let found := (reasons.findSome? Reason.error?).bind valOfErr
  pure (match found with | none => .none | some error => .some error)

/-! ## Values -/

/-- A tuple of values: the carrier's `list` frame, the one list-shaped value
(`src/Effect4/Machine/Stores.lean`; an awaited exit list, `exitsVal`, is the same frame). -/
abbrev Val.tuple (values : List Val) : Val := .list values

def Val.tuple? : Val → Option (List Val)
  | .list values => some values
  | _ => none

theorem Val.tuple?_tuple (vs : List Val) : Val.tuple? (Val.tuple vs) = some vs := rfl

theorem Val.tuple?_exact {v : Val} {vs : List Val} (h : Val.tuple? v = some vs) : v = Val.tuple vs := by
  unfold Val.tuple? at h
  split at h
  · injection h with h
    rw [h]
  · exact nomatch h

/-! ## Literals and terms -/

/-- The literals a program may write. -/
inductive Lit
  | unit
  | nat (value : Nat)
  | bool (value : Bool)
  | str (value : String)
deriving DecidableEq, Repr

/-- A variable is a position in the current environment (D1). -/
abbrev Var := Nat

mutual
  /-- A pure value: a variable, a literal, or an atom applied to values. Atoms are the
  pure functions a family declares (`AtomRow`), named, never stored. -/
  inductive Term
    | var (index : Var)
    | lit (value : Lit)
    | app (atom : String) (args : Terms)
  inductive Terms
    | nil
    | cons (head : Term) (tail : Terms)
end

deriving instance DecidableEq for Term, Terms

def Terms.toList : Terms → List Term
  | .nil => []
  | .cons head tail => head :: Terms.toList tail

/-! ## Scope: every variable of a term below a level -/

mutual
  /-- Every variable of the term is in scope at `n`. -/
  def Term.scoped (n : Nat) : Term → Bool
    | .var index => decide (index < n)
    | .lit _ => true
    | .app _ args => Terms.scoped n args
  def Terms.scoped (n : Nat) : Terms → Bool
    | .nil => true
    | .cons head tail => Term.scoped n head && Terms.scoped n tail
end


/-- A literal as a machine value: `unit`, `nat` and `bool` against the carrier's frames, and
`str` against its `string` frame. Strings are machine values on the native route since the
host rows slice (2026-09-08, DB-15): a canonical row's request and answer carry them, so a
`str` literal evaluates like every other literal (`Lit.toVal_isSome`,
`src/Effect4/Laws/Program/Typed.lean`). -/
def Lit.toVal : Lit → Option Val
  | .unit => some Val.unit
  | .nat n => some (Val.nat n)
  | .bool b => some (Val.bool b)
  | .str s => some (Val.str s)

/-! ## The atoms (DI-40) -/

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

/-! The inventory `all`, its two projections and the acceptance guards over it are generated
from this inductive's constructor list into `src/Effect4/Program/AtomInventory.lean`
(`tools/Effect4Gen/Atoms.lean`, group `AtomInventory`). Nothing below the stores reads the
list: the name lookup is a match on the string, so this module needs only the alphabet. -/

def name : NativeAtom → String
  | .succ => "succ" | .pred => "pred" | .isZero => "isZero" | .boolNot => "not"
  | .add => "add" | .lt => "lt" | .eq => "eq" | .pair => "pair"
  | .fst => "fst" | .snd => "snd" | .strings => "strings"
  | .causeIsFail => "causeIsFail" | .causeError => "causeError"
  | .causeIsDie => "causeIsDie" | .causeIsInterrupt => "causeIsInterrupt"
  | .boolOr => "or" | .boolAnd => "and"
  | .tagIs => "tagIs"
  | .isSome => "isSome" | .getOrElse => "getOrElse"

/-- Exact lookup over the complete inventory; unknown names remain refused. A match on the
string, not a scan of `all`: `evalTerm` resolves an atom at every term application, so the
lookup is on the machine's path, and OCaml compiles a string match to a decision tree where it
compiled the scan to twenty name computations and compares (`ocaml/gen/api_gen.ml:1477-1493`).
The second spelling of the name table this introduces is pinned both ways, by `ofName?_name`
(every atom's name resolves back to it) and `ofName?_sound` (a resolved name is the atom's). -/
def ofName? : String → Option NativeAtom
  | "succ" => some .succ
  | "pred" => some .pred
  | "isZero" => some .isZero
  | "not" => some .boolNot
  | "add" => some .add
  | "lt" => some .lt
  | "eq" => some .eq
  | "pair" => some .pair
  | "fst" => some .fst
  | "snd" => some .snd
  | "strings" => some .strings
  | "causeIsFail" => some .causeIsFail
  | "causeError" => some .causeError
  | "causeIsDie" => some .causeIsDie
  | "causeIsInterrupt" => some .causeIsInterrupt
  | "or" => some .boolOr
  | "and" => some .boolAnd
  | "tagIs" => some .tagIs
  | "isSome" => some .isSome
  | "getOrElse" => some .getOrElse
  | _ => none

theorem ofName?_name (atom : NativeAtom) : ofName? atom.name = some atom := by
  cases atom <;> rfl

theorem ofName?_sound {value : String} {atom : NativeAtom}
    (h : ofName? value = some atom) : atom.name = value := by
  unfold ofName? at h
  split at h <;> cases h <;> rfl

theorem name_injective {a b : NativeAtom} (h : a.name = b.name) : a = b := by
  have ha := ofName?_name a
  rw [h, ofName?_name] at ha
  exact Option.some.inj ha.symm

def arity : NativeAtom → Option Nat
  | .succ | .pred | .isZero | .boolNot | .fst | .snd
  | .causeIsFail | .causeError | .causeIsDie | .causeIsInterrupt | .isSome => some 1
  | .add | .lt | .eq | .pair | .boolOr | .boolAnd | .tagIs | .getOrElse => some 2
  | .strings => none

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

end NativeAtom

/-- String-named compatibility surface over the complete native atom inventory. -/
def nativeAtom (name : String) (values : List Val) : Option Val :=
  (NativeAtom.ofName? name).bind (fun atom => atom.eval values)

theorem nativeAtom_strings (vs : List Val) : nativeAtom "strings" vs = stringsAtom vs := rfl

/-! ## Evaluation -/

mutual
  /-- A term's value in a positional environment. -/
  def evalTerm (env : List Val) : Term → Option Val
    | .var index => env[index]?
    | .lit value => value.toVal
    | .app atom args => do
      let values ← evalTerms env args
      nativeAtom atom values
  def evalTerms (env : List Val) : Terms → Option (List Val)
    | .nil => some []
    | .cons head tail => do
      let v ← evalTerm env head
      let rest ← evalTerms env tail
      some (v :: rest)
end

end Effect4.Program
