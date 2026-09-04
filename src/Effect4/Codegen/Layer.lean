import Effect4.Program.Provision
import Effect4.Codegen.Print
import Effect4.Codegen.Spell

/-!
# Codegen.Layer — a layer term into the rc.112 `Layer` combinators

Landed 2026-09-04 from the `workshop/Provision` spike (lane C). Plan and grill:
`docs/research/2026-09-04-provision-algebra.md` §9 (R9); axiom report
`Test/Codegen/LayerPrintAxiomReport.lean`.

`Effect4/Codegen/Print.lean` takes an `Eff` program into `TypeScript.Expr`; this module takes
a `LayerTerm` (`Effect4/Program/Provision.lean`) into the same fragment. The thesis is one sentence: **a layer
term prints as the rc.112 combinators it transcribes, as syntax, never as text.** Every arm of
`printLayer` names the `vendor/effect-4.0.0-rc.112/src/Layer.ts` line it spells, and the arms
are the constructors of `LayerTerm`, one for one:

| term | rc.112 |
| --- | --- |
| `succeed key value` | `Layer.succeed(key, resource)` (`Layer.ts:1074`) |
| `effect key body` | `Layer.effect(key, effect)` (`:1427`) |
| `effectDiscard body` | `Layer.effectDiscard(effect)` (`:1512`) |
| `provide self that` | `self.pipe(Layer.provide(that))` (`:2089`, data-first `:2258`) |
| `provideMerge self that` | `self.pipe(Layer.provideMerge(that))` (`:2523`, data-first `:2704`) |
| `merge a b` | `Layer.merge(a, b)` (`:1850`), or `Layer.mergeAll(…)` (`:1652`) — see below |
| `fresh inner` | `Layer.fresh(inner)` (`:3850`) |
| `orDie inner` | `Layer.orDie(inner)` (`:3327`) |
| `App` | `Effect.provide(program, layer)` (`internal/layer.ts:8-22`, `Effect.ts:11383`) |

**The determinism discipline is the Eff printer's, unchanged.** Layout is never decided here:
the answer is `TypeScript.Expr`, which `TypeScript.Render.expr TypeScript.house0 0` renders at a
fixed layout, so equal syntax is equal bytes and no width heuristic exists anywhere in the
module. A layer body is a closed program — the layer's own scope is the ambient one
(`Layer.ts:1438`) — so every body is printed at environment length `0` and its first binder is
`a0`, exactly as `Program.print` mints it.

**The merge rule.** `mergeOperands` collects the left spine of a merge chain, the shape
`LayerTerm.mergeAll` builds (`Layer.ts:1652`, a left fold of `merge`). A merge whose left
operand is itself a merge prints as the one flat `Layer.mergeAll(…)` over that spine; a merge
whose left operand is not a merge keeps the two-argument `Layer.merge(a, b)` (`Layer.ts:1850`).
Flattening is *total* over the spine, so `merge (merge a b) c` is three operands and a chain
whose first operand is itself a merge contributes that operand's own operands too — see the
four-operand receipt at the bottom.

**What it refuses**, by constructor, never by a printed guess: `unnamedKey` is a service key
with no spelling in the supplied `KeyNames` (the printer invents no identifier, ever), and
`body` carries a `Program.PrintRefusal` out of an `effect`, an `effectDiscard`, or an `App`'s
program unchanged. There is no third refusal: every other arm of `LayerTerm` has a public
rc.112 export at this pin. In particular `orDie` **prints** — `Layer.ts:3327` is an export with
a spelling — even though `Provision.lower` refuses it, because the machine's `LayerDesc`
alphabet has no description for its `catchCause` frame. The printer's alphabet is rc.112's
public exports; the machine's is `LayerDesc`, and the two are allowed to differ.

Typing and printing stay separate: `printLayer` never consults `layerTy`. They meet only in
`printLayerDecl` and `printAppDecl`, where the declared type is read off the signature.
-/

set_option autoImplicit false

namespace Effect4.Program.Provision

open Effect4.Machine.Env (Requirement)

-- Boolean equality on a printer answer is `Effect4.Codegen.instBEqExcept`
-- (`Effect4/Codegen/Spell.lean`): every `#guard` on a printed answer below reads it.

/-! ## Key spellings as data

A `ServiceKey` is a nominal `Nat` pair (`Effect4/Machine/Key.lean`); the target spelling of the
service it names is the class identifier the service route emits,
`class Db extends Context.Service<Db, Shape>()("Db")`
(`src/Effect4/Codegen/Profile.lean:143-149`). So a key prints as `.ident name`, and the map from
keys to names is *data supplied to the printer*, never invented by it. -/

/-- The spelling of each named service key. An association list, not a function: the printer is
first-order, and `DecidableEq` holds of the whole table. -/
structure KeyNames where
  entries : List (ServiceKey × String)
deriving DecidableEq

namespace KeyNames

/-- Structural lookup in the spelling table; the first entry for a key wins. -/
def spellIn : List (ServiceKey × String) → ServiceKey → Option String
  | [], _ => none
  | (candidate, name) :: rest, key => if candidate = key then some name else spellIn rest key

/-- The service class identifier a key prints as, or `none` when the table does not name it. -/
def spell? (names : KeyNames) (key : ServiceKey) : Option String :=
  spellIn names.entries key

end KeyNames

/-! ## The refusal alphabet -/

/-- Why the layer printer declined a term. `unnamedKey` is the one refusal this module owns: a
key with no spelling has no `.ident` and the printer does not mint one. `body` is
`Program.PrintRefusal` carried out of a program body verbatim (`Effect4/Codegen/Print.lean`),
so the two refusal alphabets compose without a string anywhere. -/
inductive LayerPrintRefusal
  | unnamedKey (key : ServiceKey)
  | body (refusal : PrintRefusal)
deriving DecidableEq, Repr

/-! ## The printer -/

variable {Op : Type}

/-- The operands of a left-nested merge chain, in source order: `merge (merge a b) c` has
operands `[a, b, c]`. This is the shape `LayerTerm.mergeAll` builds (`Layer.ts:1652`: a left
fold of `merge`, so the last layer is the rightmost operand), and it is the specification of
the merge arm of `printLayer` below: that arm prints `Layer.mergeAll` over exactly this list
when the left operand is itself a merge, and the two-argument `Layer.merge` (`Layer.ts:1850`)
when it is not.

Flattening is total over the spine, which is worth stating because it surprises: a chain built
by `mergeAll` from a first operand that is *itself* a merge flattens that operand too, so
`mergeAll bindingsLayer [servicesLayer, leftWins]` has **four** operands, not three. That is
sound — `Context.merge` is right-biased and associative, so any bracketing of a left-nested
chain builds the same context — and it is canonical: every left-nested chain prints as one
`Layer.mergeAll`. -/
def mergeOperands : LayerTerm Op → List (LayerTerm Op)
  | .merge left right => mergeOperands left ++ [right]
  | leaf => [leaf]

/-- The arguments of a printed call. The merge arm applies this only to the printed left
operand of a merge whose own left operand is a merge, and the merge arm is the only arm that
prints a call headed by `Layer.merge` or `Layer.mergeAll`; so on that one call site these
arguments are exactly the printed `mergeOperands` of the left operand. (The correspondence
`callArgs ∘ printLayer = printLayer ∘ mergeOperands` on a merge is an owed theorem of the plan;
it is pinned on the witnesses below.) -/
def callArgs : TypeScript.Expr → List TypeScript.Expr
  | .call _ args => args
  | other => [other]

/-- A layer term as one TypeScript expression. Structural over `LayerTerm`; every arm names the
rc.112 export it spells. The pipeable spellings of `provide` and `provideMerge` are the ones
the corpus writes (`Layer.ts:2089`, `:2523`), and they are `.method self "pipe" [...]` rather
than a name with a dot in it, so the identifier profile still sees one identifier per name. -/
def printLayer (sig : Signature Op) (names : KeyNames) :
    LayerTerm Op → Except LayerPrintRefusal TypeScript.Expr
  -- `Layer.succeed(service, resource)` (`Layer.ts:1074`).
  | .succeed key value =>
    match names.spell? key with
    | none => .error (.unnamedKey key)
    | some name => .ok (.call (.ident "Layer.succeed") [.ident name, printLit value])
  -- `Layer.effect(service, effect)` (`Layer.ts:1427`); the body at environment length `0`.
  | .effect key body =>
    match names.spell? key with
    | none => .error (.unnamedKey key)
    | some name =>
      match Program.print sig 0 body with
      | .error refusal => .error (.body refusal)
      | .ok printed => .ok (.call (.ident "Layer.effect") [.ident name, printed])
  -- `Layer.effectDiscard(effect)` (`Layer.ts:1512`): construction work that provides nothing.
  | .effectDiscard body =>
    match Program.print sig 0 body with
    | .error refusal => .error (.body refusal)
    | .ok printed => .ok (.call (.ident "Layer.effectDiscard") [printed])
  -- `self.pipe(Layer.provide(that))` (`Layer.ts:2089`; data-first `:2258`).
  | .provide self that => do
    let s ← printLayer sig names self
    let t ← printLayer sig names that
    .ok (.method s "pipe" [.call (.ident "Layer.provide") [t]])
  -- `self.pipe(Layer.provideMerge(that))` (`Layer.ts:2523`; data-first `:2704`).
  | .provideMerge self that => do
    let s ← printLayer sig names self
    let t ← printLayer sig names that
    .ok (.method s "pipe" [.call (.ident "Layer.provideMerge") [t]])
  -- `Layer.mergeAll(…)` (`Layer.ts:1652`) along the left spine, else `Layer.merge(a, b)`
  -- (`Layer.ts:1850`). See `mergeOperands` for the rule this transcribes.
  | .merge left right => do
    let l ← printLayer sig names left
    let r ← printLayer sig names right
    match left with
    | .merge _ _ => .ok (.call (.ident "Layer.mergeAll") (callArgs l ++ [r]))
    | _ => .ok (.call (.ident "Layer.merge") [l, r])
  -- `Layer.fresh(self)` (`Layer.ts:3850`): the same signature, a private memo map.
  | .fresh inner => do
    let i ← printLayer sig names inner
    .ok (.call (.ident "Layer.fresh") [i])
  -- `Layer.orDie(self)` (`Layer.ts:3327`). Printed, though `Provision.lower` refuses it.
  | .orDie inner => do
    let i ← printLayer sig names inner
    .ok (.call (.ident "Layer.orDie") [i])

/-- `Effect.provide(program, layer)` (`vendor/effect-4.0.0-rc.112/src/internal/layer.ts:8-22`,
exported at `Effect.ts:11383`). The program is the first argument, so a refusal of the program
is the one reported when both halves refuse. -/
def printApp (sig : Signature Op) (names : KeyNames) (app : App Op) :
    Except LayerPrintRefusal TypeScript.Expr :=
  match Program.print sig 0 app.program with
  | .error refusal => .error (.body refusal)
  | .ok program => do
    let layer ← printLayer sig names app.layer
    .ok (.call (.ident "Effect.provide") [program, layer])

/-! ## The declared types

`Layer<ROut, E, RIn>` (`Layer.ts:54`) spells its two row parameters as unions of the service
class identifiers, and `never` for the empty row. `rowType` is that spelling over the row's own
canonical ascending list (`Row.elems`), so the order in the type is the key order, not the order
the term happened to mention the keys in — one more thing the printer does not decide.

The three definitions below build `String`s with `++`. That is admissible here because they feed
nothing but `TypeScript.ConstDecl.type`: no theorem of this module mentions them, and none of
them traverses a `String` (no `String.toList`, no `splitOn`, no fold) — concatenation only. -/

/-- The union spelling of a key list: `"never"` for none, the spellings joined by `" | "`
otherwise, and `none` as soon as one key is unnamed. -/
def unionType (names : KeyNames) : List ServiceKey → Option String
  | [] => some "never"
  | [key] => names.spell? key
  | key :: rest =>
    match names.spell? key, unionType names rest with
    | some head, some tail => some (head ++ " | " ++ tail)
    | _, _ => none

/-- A requirement row as a TypeScript union, in the row's canonical ascending order. -/
def rowType (names : KeyNames) (r : Requirement) : Option String :=
  unionType names r.elems

/-- `Layer.Layer<ROut, E, RIn>` (`Layer.ts:54`). The error column is `Ty.render`, the same
spelling `Effect4/Program/Eff.lean` gives every other type; the two row columns are `rowType`,
so an unnamed key anywhere in either row leaves the declaration untyped rather than guessed. -/
def layerType (names : KeyNames) (t : LayerTy) : Option String :=
  match rowType names t.out, rowType names t.requires with
  | some out, some requires =>
    some ("Layer.Layer<" ++ out ++ ", " ++ t.error.render ++ ", " ++ requires ++ ">")
  | _, _ => none

/-- The printed layer as an exported constant. `none` exactly when the layer is ill-typed
(`layerTy` refuses) or the printer refuses; a layer that prints but whose rows are not fully
named keeps its value and loses only its type annotation. -/
def printLayerDecl (name : String) (sig : Signature Op) (names : KeyNames) (l : LayerTerm Op) :
    Option TypeScript.ConstDecl :=
  match layerTy sig l, printLayer sig names l with
  | some t, .ok value =>
    some { doc := [], name := name, value := value, type := layerType names t }
  | _, _ => none

/-- The printed app as an exported constant. The type rule is `Program.printDecl`'s, reused
rather than restated: the two-parameter `Effect.Effect<A, E>` exactly when the app's requirement
row is empty — which, by `appTy_closed_iff` (`Provision.lean`), is exactly when the layer is
closed and covers the program (`appTy_closed_iff`) — and no type otherwise. -/
def printAppDecl (name : String) (sig : Signature Op) (names : KeyNames) (app : App Op) :
    Option TypeScript.ConstDecl :=
  match appTy sig app, printApp sig names app with
  | some t, .ok value => some (Program.printDecl name t value)
  | _, _ => none

/-! ## Receipts: the docs deployment of `Effect4/Program/Provision.lean`, printed

The witnesses are the ones the algebra was proved over — two platform bindings, two services
built from them, and the `POST /feedback` handler that needs both. Every pin below is on
`TypeScript.Expr` / `TypeScript.ConstDecl` *syntax*; the last two are the rendered bytes, which
the fixed-layout renderer makes a function of that syntax. -/

section Receipts

/-- The service class identifiers of the docs deployment: services `Db` and `RateLimit`, the
platform bindings `DbBinding` and `RateBinding`. -/
def docsNames : KeyNames :=
  ⟨[(dbKey, "Db"), (rateKey, "RateLimit"), (dbBinding, "DbBinding"), (rateBinding, "RateBinding")]⟩

/-- `Layer.succeed(DbBinding, 1)`. -/
def dbBindingExpr : TypeScript.Expr :=
  .call (.ident "Layer.succeed") [.ident "DbBinding", .int 1]

/-- `Layer.succeed(RateBinding, 2)`. -/
def rateBindingExpr : TypeScript.Expr :=
  .call (.ident "Layer.succeed") [.ident "RateBinding", .int 2]

/-- `Layer.merge(Layer.succeed(DbBinding, 1), Layer.succeed(RateBinding, 2))`. -/
def bindingsExpr : TypeScript.Expr :=
  .call (.ident "Layer.merge") [dbBindingExpr, rateBindingExpr]

/-- `Layer.merge(Layer.effect(Db, makeDb()), Layer.effect(RateLimit, makeRate()))`: a call row
on a `unit` request prints as `spelling()` with no argument (`printRow`). -/
def servicesExpr : TypeScript.Expr :=
  .call (.ident "Layer.merge")
    [ .call (.ident "Layer.effect") [.ident "Db", .call (.ident "makeDb") []]
    , .call (.ident "Layer.effect") [.ident "RateLimit", .call (.ident "makeRate") []] ]

/-- The deployment: `services.pipe(Layer.provideMerge(bindings))`. -/
def deploymentExpr : TypeScript.Expr :=
  .method servicesExpr "pipe" [.call (.ident "Layer.provideMerge") [bindingsExpr]]

/-- The same with the bindings hidden: `services.pipe(Layer.provide(bindings))`. -/
def hiddenExpr : TypeScript.Expr :=
  .method servicesExpr "pipe" [.call (.ident "Layer.provide") [bindingsExpr]]

/-- `leftWins`: two `Db` providers merged, the order the type cannot see (CE 5). -/
def leftWinsExpr : TypeScript.Expr :=
  .call (.ident "Layer.merge")
    [ .call (.ident "Layer.succeed") [.ident "Db", .int 1]
    , .call (.ident "Layer.succeed") [.ident "Db", .int 2] ]

/-- The handler of `POST /feedback`:
`Effect.flatMap(rateLimit.check(), (a0) => db.insertFeedback(1))` — the `bind` arm of
`Program.print` at environment length `0`, so the answer binds as `a0`. -/
def handlerExpr : TypeScript.Expr :=
  .call (.ident "Effect.flatMap")
    [ .call (.ident "rateLimit.check") []
    , .lambda ["a0"] (.call (.ident "db.insertFeedback") [.int 1]) ]

/-- `Effect.provide(handler, deployment)` (`internal/layer.ts:8-22`). -/
def appExpr : TypeScript.Expr :=
  .call (.ident "Effect.provide") [handlerExpr, deploymentExpr]

/-! ### The leaves and the two-argument merge -/

#guard printLayer docsSig docsNames bindingsLayer == .ok bindingsExpr
#guard printLayer docsSig docsNames servicesLayer == .ok servicesExpr

-- `Layer.effectDiscard(Effect.succeed(undefined))` (`Layer.ts:1512`).
#guard printLayer docsSig docsNames (.effectDiscard (.succeed (.lit .unit))) ==
  .ok (.call (.ident "Layer.effectDiscard") [.call (.ident "Effect.succeed") [.ident "undefined"]])

/-! ### The two provision spellings (`Layer.ts:2089`, `:2523`) -/

#guard printLayer docsSig docsNames deploymentLayer == .ok deploymentExpr
#guard printLayer docsSig docsNames hiddenDeployment == .ok hiddenExpr

/-! ### The merge rule -/

-- The spine of a plain merge is its two leaves; the spine of a chain is flat.
#guard mergeOperands bindingsLayer =
  [LayerTerm.succeed dbBinding (.nat 1), LayerTerm.succeed rateBinding (.nat 2)]
#guard mergeOperands (LayerTerm.mergeAll bindingsLayer [servicesLayer, leftWins]) =
  [ LayerTerm.succeed dbBinding (.nat 1), LayerTerm.succeed rateBinding (.nat 2)
  , servicesLayer, leftWins ]

-- `merge (merge a b) c` with leaf operands: one `Layer.mergeAll` with three arguments.
#guard printLayer docsSig docsNames (.merge bindingsLayer (.succeed dbKey (.nat 3))) ==
  .ok (.call (.ident "Layer.mergeAll")
    [dbBindingExpr, rateBindingExpr, .call (.ident "Layer.succeed") [.ident "Db", .int 3]])

-- `LayerTerm.mergeAll` from a first operand that is itself a merge: the spine is flattened
-- through it, so the call has four arguments, not three — `mergeOperands` above says so.
#guard printLayer docsSig docsNames (LayerTerm.mergeAll bindingsLayer [servicesLayer, leftWins]) ==
  .ok (.call (.ident "Layer.mergeAll")
    [dbBindingExpr, rateBindingExpr, servicesExpr, leftWinsExpr])

/-! ### `fresh` and `orDie`

`orDie` prints (`Layer.ts:3327` is a public export) even though the machine lowering refuses it:
`Effect4/Program/Provision.lean` pins `lower docsSig (.orDie servicesLayer) = none`, because the `LayerDesc`
alphabet has no description for a `catchCause` frame at this pin. Printing and lowering are two
different alphabets over the same term, and only lowering is short one. -/

#guard printLayer docsSig docsNames (.fresh servicesLayer) ==
  .ok (.call (.ident "Layer.fresh") [servicesExpr])
#guard printLayer docsSig docsNames (.orDie servicesLayer) ==
  .ok (.call (.ident "Layer.orDie") [servicesExpr])

/-! ### The app -/

#guard printApp docsSig docsNames theApp == .ok appExpr

/-! ### The declared types

The row order is the canonical key order (`10, 11, 20, 21`), never the order the term mentioned
the keys in. -/

#guard printAppDecl "feedback" docsSig docsNames theApp ==
  some { doc := [], name := "feedback", value := appExpr
       , type := some "Effect.Effect<void, never>" }

-- The sibling mistake leaves the app open, so the two-parameter spelling does not exist and
-- `Program.printDecl` writes no type — the same rule, unchanged, over a layer-provided program.
#guard (printAppDecl "broken" docsSig docsNames ⟨siblingMistake, feedbackHandler⟩).map
    TypeScript.ConstDecl.type == some none

#guard printLayerDecl "deployment" docsSig docsNames deploymentLayer ==
  some { doc := [], name := "deployment", value := deploymentExpr
       , type := some "Layer.Layer<Db | RateLimit | DbBinding | RateBinding, never, never>" }

#guard (printLayerDecl "services" docsSig docsNames servicesLayer).map
    TypeScript.ConstDecl.type ==
  some (some "Layer.Layer<Db | RateLimit, never, DbBinding | RateBinding>")

#guard rowType docsNames Requirement.empty == some "never"
#guard rowType ⟨[]⟩ (Requirement.single dbKey) == none

/-! ### Refusals are data -/

-- An empty spelling table names nothing, and the printer mints no identifier: the left operand
-- refuses first, by key.
#guard printLayer docsSig ⟨[]⟩ bindingsLayer == .error (.unnamedKey dbBinding)

-- A body refusal travels out of the layer unchanged (`choose` is flows-only, D2).
#guard printLayer docsSig docsNames
    (.effect dbKey (.choose 7 (.succeed (.lit .unit)) (.succeed (.lit .unit)))) ==
  .error (.body (.choose 7))

/-! ### The rendered bytes

Two readability pins only: the renderer is a function of the syntax above, so these add no
information the structural receipts lack — they say what the syntax looks like. -/

#guard TypeScript.Render.expr TypeScript.house0 0 bindingsExpr ==
  "Layer.merge(Layer.succeed(DbBinding, 1), Layer.succeed(RateBinding, 2))"

#guard TypeScript.Render.expr TypeScript.house0 0 deploymentExpr ==
  "Layer.merge(Layer.effect(Db, makeDb()), Layer.effect(RateLimit, makeRate())).pipe(Layer.provideMerge(Layer.merge(Layer.succeed(DbBinding, 1), Layer.succeed(RateBinding, 2))))"

end Receipts

/-! ## Separation gate: the printer's own alphabet is first-order data -/

example : DecidableEq KeyNames := inferInstance
example : DecidableEq LayerPrintRefusal := inferInstance

end Effect4.Program.Provision
