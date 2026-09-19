import Effect4.Program.Ty
import Effect4.Program.AtomInventory

/-!
# Native atom typing (DI-40)

The typing half of the atom table: each atom's typing *scheme* as first-order data (`Scheme`),
the specification row that carries it (`Spec`, `spec`), `typeOf` as the scheme applied, and the
table's own structural well-formedness (`specWellFormed`, `atomWellFormed`, `atom_table_wf`).

The alphabet itself — the inductive, the data row `AtomRow`, the name, the arity, the
const-generic flag, the name lookup and `eval` — is `Machine/Term.lean`, below the stores; the
inventory `all` and its projections are generated from that inductive's constructor list into
`Program/AtomInventory.lean`. Nothing of the type language reaches the runtime half, so the
machine's import closure, and the LCNF cut taken from it, does not carry the checker.

The scheme language is the row-template calculus of decisions row 42, not a second one:
`Ty.var`, `Ty.instantiate`, `Ty.infer` and `Ty.matchTemplate` are the rows' (`Program/Ty.lean`),
and `Ty.matchTemplateArgs` (`Ty.lean`, beside `matchTemplate`) is its list-level fold. One
calculus, two consumers.

A scheme deliberately does not **normalise** the instantiated answer: normalising would
change the typing judgment, since `normalize` distributes a product over a union, and that is
rows 42/43 calculus scheduled with L4, not a refactor of what the table says today. What it
does choose is how a parameter repeated across the arguments binds (`Scheme.poly`'s `join`):
the prelude's own declaration decides, `NoInfer` or not.

`all_complete` forces an appended constructor into the inventory, `Scheme.apply` is total, and
every dispatch here covers the enum explicitly, so a new constructor cannot inherit a fallback.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- The two input families advertised by the cause query atoms. -/
def causeInputError? : Ty → Option Ty
  | .causeOf error | .exitOf _ error => some error
  | _ => none

namespace NativeAtom

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

/-- The atoms whose typing is not a template. Each names the rule it is, so the scheme stays
first-order data and the rule stays one definition. These are the awkward ones the table does
not make cheaper — it stops them from being spread across five matches, and no more. -/
inductive CustomScheme
  /-- `fst`/`snd`: distribute over unions and join the selected columns (`projectProduct`). -/
  | project (second : Bool)
  /-- `causeIsFail`/`causeIsDie`/`causeIsInterrupt`: a cause or a failed exit in, a Boolean
  out; the input family is `causeInputError?`. -/
  | causeTest
  /-- `causeError`: the same input, an option of its error column out. -/
  | causeError
deriving DecidableEq, Repr

/-- The arity each custom rule accepts, so the table's `arity` column is checked against the
rule rather than trusted (`specWellFormed`). -/
def CustomScheme.declaredArity : CustomScheme → Option Nat
  | .project _ => some 1
  | .causeTest => some 1
  | .causeError => some 1

/-! Each rule is its own definition over the argument list, so "one rule, one definition" is
literally true and a proof about one rule splits that rule's arms and no others. The input
classifiers they read (`projectProduct`, `causeInputError?`) match a *head*, so their negative
class is a wildcard — the positive arms are explicit and the default absorbs everything else,
which is the shape DI-95 settled for a classifier. -/

/-- `fst`/`snd`. -/
def projectRule (second : Bool) : List Ty → Option Ty
  | [a] => projectProduct second a
  | [] | _ :: _ :: _ => none

/-- `causeIsFail`/`causeIsDie`/`causeIsInterrupt`. -/
def causeTestRule : List Ty → Option Ty
  | [input] => (causeInputError? input).map fun _ => .bool
  | [] | _ :: _ :: _ => none

/-- `causeError`. -/
def causeErrorRule : List Ty → Option Ty
  | [input] => (causeInputError? input).map Ty.option
  | [] | _ :: _ :: _ => none

/-- The custom rules, verbatim from the arms they replace. -/
def CustomScheme.apply : CustomScheme → List Ty → Option Ty
  | .project second => projectRule second
  | .causeTest => causeTestRule
  | .causeError => causeErrorRule

/-- A fixed signature applied: each argument at a subtype of its parameter (`Ty.sub` is
TypeScript assignability at a call site, so `succ` takes a `nat` and therefore a `never`). -/
def monoApply (params : List Ty) (answer : Ty) (tys : List Ty) : Option Ty :=
  if tys.length = params.length ∧ (tys.zip params).all (fun (a, e) => a.sub e) then some answer
  else none

/-- An atom's typing scheme, as data. -/
inductive Scheme
  /-- Fixed parameters, fixed answer. -/
  | mono (params : List Ty) (answer : Ty)
  /-- Any number of arguments at one parameter type. -/
  | variadic (param answer : Ty)
  /-- A template over `Ty.var`: the parameters bind by `Ty.matchTemplateArgs` and the answer is
  instantiated at the bindings. `join` is the prelude's inference at a repeated parameter:
  `true` where it declares a plain `<A>` (the candidates' common supertype, `Ty.infer`),
  `false` where a later occurrence is `NoInfer<A>` (the first binding stays). -/
  | poly (params : List Ty) (answer : Ty) (join : Bool := false)
  /-- Alternative fixed signatures, first hit wins. -/
  | alts (cases : List (List Ty × Ty))
  /-- A named rule. -/
  | custom (tag : CustomScheme)
deriving DecidableEq, Repr

/-- The scheme at an argument list: the executable typing of every atom. -/
def Scheme.apply : Scheme → List Ty → Option Ty
  | .mono params answer, tys => monoApply params answer tys
  | .variadic param answer, tys => if tys.all (·.sub param) then some answer else none
  | .poly params answer join, tys =>
    (Ty.matchTemplateArgs [] params tys join).map fun σ => Ty.instantiate σ answer
  | .alts cases, tys => cases.findSome? fun c => monoApply c.1 c.2 tys
  | .custom tag, tys => tag.apply tys

/-- The monomorphic signature a scheme declares, when it declares one. -/
def Scheme.monoSig : Scheme → Option (List Ty × Ty)
  | .mono params answer => some (params, answer)
  | .variadic _ _ | .poly .. | .alts _ | .custom _ => none

/-- The arity the scheme declares agrees with the table's own `arity` column. -/
def Scheme.arityAgrees (s : Scheme) (arity : Option Nat) : Bool :=
  match s with
  | .mono params _ => arity == some params.length
  | .poly params _ .. => arity == some params.length
  | .variadic _ _ => arity == none
  | .alts cases => cases.all fun c => arity == some c.1.length
  | .custom tag => arity == tag.declaredArity

/-- The scheme answers its own declared answer at its own declared parameters: a template
instantiates to what it says, an alternative types at itself, a fixed signature is reflexive,
and a variadic one accepts two of its parameter. A custom rule declares nothing here and is
answered by its own laws. -/
def Scheme.answersDeclared (s : Scheme) : Bool :=
  match s with
  | .mono params answer => s.apply params == some answer
  | .poly params answer .. => s.apply params == some answer
  | .variadic param answer => s.apply [param, param] == some answer
  | .alts cases => cases.all fun c => s.apply c.1 == some c.2
  | .custom _ => true

/-- One atom's typing specification: where its meaning comes from, and what it transcribes.
The `cite` column is rendered as the doc comment of the generated TypeScript prelude entry, so
the face carries the citation the table carries. -/
structure Spec where
  scheme : Scheme
  cite : String
deriving DecidableEq, Repr

/-- The table. One exhaustive match; `typeOf` and `mono` are projections of it.

Each row's scheme answers exactly what the hand-written arm of `typeOf` answered, at every
argument list. Three of them are worth a sentence. `eq` is `alts`, because its two signatures
are tried in order and both answer `bool`. `pair` is `poly` over two distinct parameters, so
`matchTemplateArgs` binds them positionally and no join ever fires — `typeOf .pair [a, b]` is
`prod a b`, which is what DI-55 and the `eq (fst (pair "A" m)) "A"` idiom stand on. `tagIs` is
`mono` at `[.string, .unknown]` — the second parameter is the top (decisions row 46), which
every type is below, so the arm that used to ignore its second argument is now a signature the
prelude's own `(tag: string, e: unknown)` spells the same way. -/
def spec : NativeAtom → Spec
  | .succ => { scheme := .mono [.nat] .nat,
               cite := "`\"succ\", [nat n] => nat (n + 1)`" }
  | .pred => { scheme := .mono [.nat] .nat,
               cite := "`\"pred\", [nat n] => nat (n - 1)` — Lean `Nat` subtraction truncates \
                        at zero." }
  | .isZero => { scheme := .mono [.nat] .bool,
                 cite := "`\"isZero\", [nat n] => bool (n = 0)`" }
  | .boolNot => { scheme := .mono [.bool] .bool,
                  cite := "`\"not\", [bool b] => bool (!b)`" }
  | .add => { scheme := .mono [.nat, .nat] .nat,
              cite := "`\"add\", [nat a, nat b] => nat (a + b)`" }
  | .lt => { scheme := .mono [.nat, .nat] .bool,
             cite := "`\"lt\", [nat a, nat b] => bool (a < b)`" }
  | .eq => { scheme := .alts [([.nat, .nat], .bool), ([.string, .string], .bool)],
             cite := "NativeAtom.eq on admitted natural or string pairs (DI-09)." }
  | .pair =>
      { scheme := .poly [.var 0, .var 1] (.prod (.var 0) (.var 1)),
        cite := "`\"pair\", [a, b] => Val.tuple [a, b]` — a two-element tuple, the wire's JSON \
                 array.\nThe type parameters are `const` (DI-55, DI-15's literal rule, part 4 \
                 2026-09-12): a string\nliteral argument keeps its literal type, so \
                 `pair(\"A\", m)` is `readonly [\"A\", string]` and\n`pair(\"A\", \"m\")` is \
                 `readonly [\"A\", \"m\"]`, exactly what `NativeAtom.typeOf .pair` answers\n\
                 under `litArgTy`; a `string` variable stays `string`." }
  | .fst => { scheme := .custom (.project false),
              cite := "`\"fst\", [exitCons a _] => a`" }
  | .snd => { scheme := .custom (.project true),
              cite := "`\"snd\", [exitCons _ (exitCons b _)] => b`" }
  | .strings =>
      { scheme := .variadic .string (.list .string),
        cite := "`\"strings\", vs => list vs` — also the parameter list of a host row, JSON \
                 texts (DB-15)." }
  | .causeIsFail =>
      { scheme := .custom .causeTest,
        cite := "NativeAtom.causeIsFail; rc.112 internal/effect.ts:148 (any Fail, not Fail \
                 only)." }
  | .causeError =>
      { scheme := .custom .causeError,
        cite := "NativeAtom.causeError; rc.112 internal/effect.ts:157-168 selects the first \
                 Fail.\nLean's unrepresentable boom is an explicit model boundary, not a host \
                 string value." }
  | .causeIsDie =>
      { scheme := .custom .causeTest,
        cite := "NativeAtom.causeIsDie; rc.112 internal/effect.ts:171." }
  | .causeIsInterrupt =>
      { scheme := .custom .causeTest,
        cite := "NativeAtom.causeIsInterrupt; rc.112 internal/effect.ts:186." }
  | .boolOr => { scheme := .mono [.bool, .bool] .bool,
                 cite := "NativeAtom.boolOr; all inputs are pure evaluated Boolean values." }
  | .boolAnd => { scheme := .mono [.bool, .bool] .bool,
                  cite := "NativeAtom.boolAnd; all inputs are pure evaluated Boolean values." }
  | .tagIs =>
      { scheme := .mono [.string, .unknown] .bool,
        cite := "NativeAtom.tagIs: true exactly on a pair whose first component is the tag\n\
                 (`.list [.str tag, _]`, `NativeAtom.tagHit`). This ordinary Boolean test \
                 carries no\nrefinement promise. In particular, catchIf's first-failure test \
                 does not establish\nthat every failure in a re-raised cause excludes this tag \
                 (DI-17, DI-39)." }
  | .isSome =>
      { scheme := .mono [.option .unknown] .bool,
        cite := "NativeAtom.isSome: presence only, with no TypeScript branch refinement.\n\
                 Pinned implementation: vendor/effect-4.0.0-rc.112/src/Option.ts (isSome)." }
  | .getOrElse =>
      { scheme := .poly [.option (.var 0), .var 0] (.var 0),
        cite := "NativeAtom.getOrElse: the payload type fixes the default and result. Both \
                 call\narguments are evaluated eagerly; this thunk captures only the already \
                 evaluated default.\nPinned implementation: \
                 vendor/effect-4.0.0-rc.112/src/Option.ts (getOrElse)." }
  | .ite =>
      { scheme := .poly [.bool, .var 0, .var 0] (.var 0) true,
        cite := "`\"ite\", [bool c, a, b] => if c then a else b` — a selection between two \
                 evaluated\narguments, not a lazy conditional." }
  | .optSome =>
      { scheme := .poly [.var 0] (.option (.var 0)),
        cite := "`\"some\", [a] => some a` — Option.some (vendor/effect-4.0.0-rc.112/src/Option.ts)." }
  | .optNone =>
      { scheme := .mono [] (.option .never),
        cite := "`\"none\", [] => none` — Option.none (vendor/effect-4.0.0-rc.112/src/Option.ts)." }
  | .mul =>
      { scheme := .mono [.nat, .nat] .nat,
        cite := "`\"mul\", [nat a, nat b] => nat (a * b)`" }
  | .listNil =>
      { scheme := .mono [] (.list .never),
        cite := "`\"nil\", [] => list []`" }
  | .listCons =>
      { scheme := .poly [.var 0, .list (.var 0)] (.list (.var 0)) true,
        cite := "`\"cons\", [x, list vs] => list (x :: vs)` — a fiber snapshot is the list of its \
                 handles\n(`Val.asList?`)." }
  | .listGet =>
      { scheme := .poly [.list (.var 0), .nat] (.option (.var 0)),
        cite := "`\"get\", [list vs, nat i] => option vs[i]?` — rc.112 `Array.get` at a natural \
                 index\n(vendor/effect-4.0.0-rc.112/src/Array.ts:1698)." }
  | .listLength =>
      { scheme := .mono [.list .unknown] .nat,
        cite := "`\"length\", [list vs] => nat vs.length`" }
  | .listAppend =>
      { scheme := .poly [.list (.var 0), .list (.var 0)] (.list (.var 0)) true,
        cite := "`\"append\", [list xs, list ys] => list (xs ++ ys)`" }
  | .natSub =>
      { scheme := .mono [.nat, .nat] .nat,
        cite := "`\"sub\", [nat a, nat b] => nat (a - b)` — Lean `Nat` subtraction truncates at \
                 zero." }
  | .natDiv =>
      { scheme := .mono [.nat, .nat] .nat,
        cite := "`\"div\", [nat a, nat b] => nat (a / b)` — Lean `Nat` division answers zero at a \
                 zero divisor." }
  | .natMod =>
      { scheme := .mono [.nat, .nat] .nat,
        cite := "`\"mod\", [nat a, nat b] => nat (a % b)` — Lean `Nat` remainder answers the \
                 dividend at a zero divisor." }
  | .strConcat =>
      { scheme := .mono [.string, .string] .string,
        cite := "`\"concat\", [str a, str b] => str (a ++ b)`" }

/-- The typing of an application by its argument types (DI-40; DI-15, the 2026-09-12 clause):
the atom's scheme, applied. -/
def typeOf (atom : NativeAtom) : List Ty → Option Ty := (spec atom).scheme.apply

/-- Monomorphic metadata for generated interfaces. Polymorphic schemes are `none`;
`typeOf` remains their single executable typing owner. -/
def mono (atom : NativeAtom) : Option (List Ty × Ty) := (spec atom).scheme.monoSig

/-- A monomorphic row's typing is exactly argument-wise subsumption (`mono`, `typeOf`). -/
theorem typeOf_mono (atom : NativeAtom) (args answer : _) (h : atom.mono = some (args, answer))
    (tys : List Ty) :
    typeOf atom tys =
      if tys.length = args.length ∧ (tys.zip args).all (fun (a, e) => a.sub e) then some answer
      else none := by
  unfold mono Scheme.monoSig at h
  split at h
  case h_1 params ans heq =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [typeOf, heq, Scheme.apply, monoApply]
  -- every other scheme declares no monomorphic signature
  all_goals exact nomatch h

/-! ## The table's own well-formedness (the tooling plan 2.1)

Four structural obligations, decided once over the whole inventory rather than argued per atom.
They are the invariants a reader of the table may assume and an appended atom must satisfy;
what they are *not* is the semantic obligation (`typeOf` answers a type the atom's `eval`
inhabits), which quantifies over all `Ty` and all `Val` and is therefore not decidable at all —
that one is `NativeAtom.Sound` in `Laws/Program/Typed.lean`. -/

/-- Every structural obligation on one row of the table, as a Boolean over the row's own
columns and an ambient inventory of names:

* the name occurs exactly once in the inventory, so `ofName?` cannot be ambiguous;
* the arity column agrees with the arity the scheme declares;
* the scheme answers its own declared answer at its own declared parameters, so the scheme is
  metadata about `typeOf` rather than a second, drifting, typing rule;
* a const-generic row has no monomorphic signature (DI-55: the literal rule only has content
  where a parameter is polymorphic).

Stated over `(AtomRow, Spec)` rather than over `NativeAtom`, so the red control in
`Test/Program/AtomTable.lean` exercises *this* predicate on rows built by hand. -/
def specWellFormed (inventory : List String) (r : AtomRow) (s : Spec) : Bool :=
  (inventory.count r.name == 1)
    && s.scheme.arityAgrees r.arity
    && s.scheme.answersDeclared
    && (!r.constGeneric || s.scheme.monoSig.isNone)

/-- The obligations at one atom of the real table. -/
def atomWellFormed (atom : NativeAtom) : Bool :=
  specWellFormed names (row atom) (spec atom)

/-- The whole table is well-formed. Decided in the kernel: `specWellFormed` compares `String`s,
whose `DecidableEq` goes through `List Char`, and the elaborator's whnf expands a string
literal per character (`Lean/Meta/WHNF.lean`), so the reduction belongs where it is cheapest. -/
theorem atom_table_wf : NativeAtom.all.all atomWellFormed = true := by decide +kernel

end NativeAtom
end Effect4.Program
