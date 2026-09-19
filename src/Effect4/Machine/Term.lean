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
  /-- L4-blocking atoms (DI-40, DI-78): conditional, option constructors, multiplication. -/
  | ite | optSome | optNone | mul
  /-- The L3 atoms (plan §2.6): the list operations, which read a fiber snapshot as the list of
  its handles (`Val.asList?`), the rest of natural arithmetic, and string concatenation. -/
  | listNil | listCons | listGet | listLength | listAppend | natSub | natDiv | natMod | strConcat
  deriving DecidableEq, BEq

namespace NativeAtom

/-! The inventory `all`, its two projections and the acceptance guards over it are generated
from this inductive's constructor list into `src/Effect4/Program/AtomInventory.lean`
(`tools/Effect4Gen/Atoms.lean`, group `AtomInventory`). Nothing below the stores reads the
list: the name lookup is a match on the string, so this module needs only the alphabet. -/

/-- One atom's data: everything about an atom that is neither a type nor its evaluation, in
one row instead of four matches.

Three things the record deliberately does not hold. **No function field** — an
`eval : List Val → Option Val` column would take `eval` off the enum, and with it the
compiler's exhaustiveness error (the one mechanism that has caught every omission in this
alphabet) and the OCaml engine's jump table, since LCNF's mono phase cannot see through a
closure read out of a table row (`ocaml/gen/api_gen.ml`, the lowering of `eval`). **No `Ty`**
— the type language stays above the stores, so the machine's import closure, and the LCNF cut
taken from it, does not carry the checker; the typing half is `Program/NativeAtom.lean`. **No
citation** — that belongs with the typing rule it transcribes (`NativeAtom.Spec.cite`). -/
structure AtomRow where
  /-- The atom's name: its spelling on the wire, in the generated profile, in the OCaml
  alphabet and in the TypeScript prelude. -/
  name : String
  /-- `some n` for a fixed arity, `none` for a variadic atom. -/
  arity : Option Nat
  /-- The literal rule's flag (DI-55, the prelude's `pair<const A, const B>`): a string literal
  argument keeps its literal type under `litArgTy` (DI-15). Only `pair` is; every other atom
  widens a literal to `string`, as TypeScript does at a non-`const` parameter. -/
  constGeneric : Bool
  /-- The atom's body in the TypeScript prelude: the text after `export const <name> = `.
  `harness/truth/prelude-atoms.gen.ts` is this column, one line per atom. -/
  prelude : String
deriving DecidableEq, Repr

/-- The table. One exhaustive match, so an appended constructor is a compile error here and
nowhere else; `name`, `arity` and `constGeneric` are projections of it. -/
def row : NativeAtom → AtomRow
  | .succ => { name := "succ", arity := some 1, constGeneric := false,
               prelude := "(n: number): number => n + 1" }
  | .pred => { name := "pred", arity := some 1, constGeneric := false,
               prelude := "(n: number): number => (n === 0 ? 0 : n - 1)" }
  | .isZero => { name := "isZero", arity := some 1, constGeneric := false,
                 prelude := "(n: number): boolean => n === 0" }
  | .boolNot => { name := "not", arity := some 1, constGeneric := false,
                  prelude := "(b: boolean): boolean => !b" }
  | .add => { name := "add", arity := some 2, constGeneric := false,
              prelude := "(a: number, b: number): number => a + b" }
  | .lt => { name := "lt", arity := some 2, constGeneric := false,
             prelude := "(a: number, b: number): boolean => a < b" }
  | .eq => { name := "eq", arity := some 2, constGeneric := false,
             prelude := "(a: number | string, b: number | string): boolean => a === b" }
  | .pair => { name := "pair", arity := some 2, constGeneric := true,
               prelude := "<const A, const B>(a: A, b: B): readonly [A, B] => [a, b]" }
  | .fst => { name := "fst", arity := some 1, constGeneric := false,
              prelude := "<P extends readonly [unknown, unknown]>(p: P): P[0] => p[0]" }
  | .snd => { name := "snd", arity := some 1, constGeneric := false,
              prelude := "<P extends readonly [unknown, unknown]>(p: P): P[1] => p[1]" }
  | .strings => { name := "strings", arity := none, constGeneric := false,
                  prelude := "(...texts: string[]): ReadonlyArray<string> => texts" }
  | .causeIsFail =>
      { name := "causeIsFail", arity := some 1, constGeneric := false,
        prelude := "<A, E>(input: Cause.Cause<E> | Exit.Exit<A, E>): boolean =>\n  \
                    Cause.hasFails(queryCause(input))" }
  | .causeError =>
      { name := "causeError", arity := some 1, constGeneric := false,
        prelude := "<A, E>(input: Cause.Cause<E> | Exit.Exit<A, E>): Option.Option<E> =>\n  \
                    Cause.findErrorOption(queryCause(input))" }
  | .causeIsDie =>
      { name := "causeIsDie", arity := some 1, constGeneric := false,
        prelude := "<A, E>(input: Cause.Cause<E> | Exit.Exit<A, E>): boolean =>\n  \
                    Cause.hasDies(queryCause(input))" }
  | .causeIsInterrupt =>
      { name := "causeIsInterrupt", arity := some 1, constGeneric := false,
        prelude := "<A, E>(input: Cause.Cause<E> | Exit.Exit<A, E>): boolean =>\n  \
                    Cause.hasInterrupts(queryCause(input))" }
  | .boolOr => { name := "or", arity := some 2, constGeneric := false,
                 prelude := "(a: boolean, b: boolean): boolean => a || b" }
  | .boolAnd => { name := "and", arity := some 2, constGeneric := false,
                  prelude := "(a: boolean, b: boolean): boolean => a && b" }
  | .tagIs => { name := "tagIs", arity := some 2, constGeneric := false,
                prelude := "(tag: string, e: unknown): boolean =>\n  \
                            Array.isArray(e) && e.length === 2 && e[0] === tag" }
  | .isSome => { name := "isSome", arity := some 1, constGeneric := false,
                 prelude := "(value: Option.Option<unknown>): boolean => Option.isSome(value)" }
  | .getOrElse =>
      { name := "getOrElse", arity := some 2, constGeneric := false,
        prelude := "<A>(value: Option.Option<A>, fallback: NoInfer<A>): A =>\n  \
                    Option.getOrElse(value, () => fallback)" }
  | .ite =>
      { name := "ite", arity := some 3, constGeneric := false,
        prelude := "<A>(c: boolean, t: A, f: A): A => (c ? t : f)" }
  | .optSome =>
      { name := "some", arity := some 1, constGeneric := false,
        prelude := "<A>(value: A): Option.Option<A> => Option.some(value)" }
  | .optNone =>
      { name := "none", arity := some 0, constGeneric := false,
        prelude := "(): Option.Option<never> => Option.none()" }
  | .mul =>
      { name := "mul", arity := some 2, constGeneric := false,
        prelude := "(a: number, b: number): number => a * b" }
  | .listNil =>
      { name := "nil", arity := some 0, constGeneric := false,
        prelude := "(): ReadonlyArray<never> => []" }
  | .listCons =>
      { name := "cons", arity := some 2, constGeneric := false,
        prelude := "<A>(x: A, xs: ReadonlyArray<A>): ReadonlyArray<A> => [x, ...xs]" }
  | .listGet =>
      { name := "get", arity := some 2, constGeneric := false,
        prelude := "<A>(xs: ReadonlyArray<A>, i: number): Option.Option<A> =>\n  \
                    (i < xs.length ? Option.some(xs[i] as A) : Option.none())" }
  | .listLength =>
      { name := "length", arity := some 1, constGeneric := false,
        prelude := "(xs: ReadonlyArray<unknown>): number => xs.length" }
  | .listAppend =>
      { name := "append", arity := some 2, constGeneric := false,
        prelude := "<A>(xs: ReadonlyArray<A>, ys: ReadonlyArray<A>): ReadonlyArray<A> =>\n  \
                    [...xs, ...ys]" }
  | .natSub =>
      { name := "sub", arity := some 2, constGeneric := false,
        prelude := "(a: number, b: number): number => (a <= b ? 0 : a - b)" }
  | .natDiv =>
      { name := "div", arity := some 2, constGeneric := false,
        prelude := "(a: number, b: number): number => (b === 0 ? 0 : Math.floor(a / b))" }
  | .natMod =>
      { name := "mod", arity := some 2, constGeneric := false,
        prelude := "(a: number, b: number): number => (b === 0 ? a : a % b)" }
  | .strConcat =>
      { name := "concat", arity := some 2, constGeneric := false,
        prelude := "(a: string, b: string): string => a + b" }

def name (atom : NativeAtom) : String := (row atom).name

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
  | "ite" => some .ite
  | "some" => some .optSome
  | "none" => some .optNone
  | "mul" => some .mul
  | "nil" => some .listNil
  | "cons" => some .listCons
  | "get" => some .listGet
  | "length" => some .listLength
  | "append" => some .listAppend
  | "sub" => some .natSub
  | "div" => some .natDiv
  | "mod" => some .natMod
  | "concat" => some .strConcat
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

def arity (atom : NativeAtom) : Option Nat := (row atom).arity

/-- Whether the atom's parameters are const-generic (DI-55). A projection of the table; it is
lifted by name in `nativeConstAtom` (`Program/Native.lean`) and read by the literal rule. -/
def constGeneric (atom : NativeAtom) : Bool := (row atom).constGeneric

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
  | .ite, [Val.bool c, a, b] => some (if c then a else b)
  | .optSome, [a] => some (Store.Val.some a)
  | .optNone, [] => some Store.Val.none
  | .mul, [Val.nat a, Val.nat b] => some (Val.nat (a * b))
  | .listNil, [] => some (Val.list [])
  | .listCons, [x, xs] => (Val.asList? xs).map fun vs => Val.list (x :: vs)
  | .listGet, [xs, Val.nat i] =>
    (Val.asList? xs).map fun vs => (match vs[i]? with
      | some v => Store.Val.some v
      | none => Store.Val.none)
  | .listLength, [xs] => (Val.asList? xs).map fun vs => Val.nat vs.length
  | .listAppend, [xs, ys] =>
    (Val.asList? xs).bind fun front => (Val.asList? ys).map fun back => Val.list (front ++ back)
  | .natSub, [Val.nat a, Val.nat b] => some (Val.nat (a - b))
  | .natDiv, [Val.nat a, Val.nat b] => some (Val.nat (a / b))
  | .natMod, [Val.nat a, Val.nat b] => some (Val.nat (a % b))
  | .strConcat, [Val.str a, Val.str b] => some (Val.str (a ++ b))
  | .succ, _ | .pred, _ | .isZero, _ | .boolNot, _ | .add, _ | .lt, _ | .eq, _
  | .pair, _ | .fst, _ | .snd, _
  | .causeIsFail, _ | .causeError, _ | .causeIsDie, _ | .causeIsInterrupt, _
  | .boolOr, _ | .boolAnd, _ | .tagIs, _ | .isSome, _ | .getOrElse, _
  | .ite, _ | .optSome, _ | .optNone, _ | .mul, _
  | .listNil, _ | .listCons, _ | .listGet, _ | .listLength, _ | .listAppend, _
  | .natSub, _ | .natDiv, _ | .natMod, _ | .strConcat, _ => none

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
