# The generation medium: schemas and AST transforms as the meta language

Workshop note, 2026-09-16 late night, at `6657e5a9`. The owner accepted the needs round of
the layout note (`2026-09-16-system-layout-and-abstractions.md` §5) as recommended, with one
rule on top: keep it simple, do the most basic thing the algebraic constructions offer, and
add features as they are discovered. Then three asks, in their words condensed:

1. "We have a starting schema; translate arbitrary Eff programs into the AST; reduce all of
   our codegen to be contained on a schema with APIs; the API is the AST compiler that can
   run; a medium where we can jump between Effect and static data; the schema AST API is one
   of the core constructs we need to work on; workshop it ahead of time." The MCP server
   itself "as a bun Effect MCP, which we'll want to generate again".
2. "That might actually become the TypeScript. Let's see how much we can generate in that
   form from the LCNF. Your codegen becomes its own meta language, spoken in schemas and AST
   transforms."
3. "Let's get the whole Effect: Mailbox, PubSub, Queue. That should all be in our Lean."

This note names the construct (§1), shows the medium (§2), gives the TypeScript form
concretely (§3), measures how much of the surface already has that form and how the rest is
classified (§4), puts the Effect modules through the same construct (§5), lists what exists
and what is missing per host (§6), proposes the order (§7), and ends with the questions to
workshop (§8).

---

## 1. The construct: five words per signature

Everything the system generates is one of five things for some signature. A signature `Sig`
is a list of families, each a list of constructors, each a list of fields with a carrier
(another family, or a base type). That is exactly what `OCaml5.Eff.World.Spec` and `blocks`
already read off the Lean environment for the `Eff` IR, and what `tools/Tools/TsGen.lean`
and `src/OCaml5/Tools/EffGen.lean` both consume: the closed world of 28 families.

| word | what it is | Lean today | TypeScript today | OCaml today |
| --- | --- | --- | --- | --- |
| `Schema(Sig)` | the type of terms: the initial algebra | the inductives (`Program/Eff.lean` and companions) | `eff.gen.ts`: one `Schema` and one type per family, tagged unions with `_tag`, `ReadonlyArray` for `nil`/`cons`, string-literal unions for nullary families | `eff_types.ml` |
| `Algebra(Sig, R)` | one function per constructor with every child replaced by `R[fam]`; the carrier is a family of types | `EffAlgebra Op R` with `R : EffFam → Type` (`Fold.lean:940`, generated) | missing | missing (blocked: `unsupported parameter R`) |
| `fold(Sig)` | the catamorphism: `Algebra(Sig, R) → Term → R[fam]` | `cata_eff` and one per family (`Fold.lean:1008`), `foldMapAt_eff` with paths | missing | missing |
| `Hom(Sig)` | uniqueness of the fold and fusion: `hom_eq_cata`, `cata_id`, `AlgMap`, `cata_fusion` | `hom_eq_cata_eff`, `cata_id_*` generated; `AlgMap`/`cata_eff_fusion` missing (present for `Doc`) | missing (as guards on the corpus) | missing |
| `Build(Sig)` | the constructors as a typed API that produces terms | the authoring lifts over `binders.json` (generated, scope-safe) | missing (terms are written as object literals; `read.ts` produces them from text) | `eff_types.ml` constructors |

Everything else is an **instance**: an `Algebra(Sig, R)` for a chosen `R`, applied through
`fold`. The instances the estate has or needs, all over `Sig = Eff` unless said:

| instance | carrier `R` | what it is | today |
| --- | --- | --- | --- |
| `id` | the terms themselves | `cata id = id` (law) | generated |
| `weaken`, `expandRound`, `refSites`, `layerPaths`, `frontierMap` | terms, lists of paths | the universal-algebra refactor's transforms | through the fold |
| `effTy` | `TyEnv → Option EffTy` | typing with an environment: the exponential carrier | hand-written `match` in a `mutual` (`Typing.lean:284`) |
| `explain`, `blame` | `Option TypeRefusal`, `Option Path` | the first refusal as a projection of the typing fold | hand-written, laws proved (DI-86) |
| `compileEff` | `Point → NCode` | the machine's code, with the point as parameter | hand-written (`Compile.lean:543`) |
| `denote` | `List Val → Effects.Program StoreSig ExitV` | the meaning, into the free monad with an environment | hand-written (`Denote.lean:66`) |
| `Straight` | `Bool` | the straight-fragment predicate | hand-written (`Fragment.lean:20`) |
| `print` | `Nat → Except PrintRefusal Tree` | the template table with the depth as parameter | hand-written (`Print.lean:317`); R4 makes it rows |
| `read` (over `Sig = Tree`) | `Nat → Except ReadRefusal Eff` | the generic inverse of the table | hand-written (`Read.lean:393`); R5 |
| `toJson`, `wire` | `String`, bytes | the codecs | generated on all three hosts, as loops with a work stack |
| `run` (host) | `Effect.Effect<A, E, R>` | the AST compiler that can run: a program as data executed by the Effect runtime | missing; today a program runs only as printed text |
| `render` (over `Sig = Tree`), `layout` (over `Sig = Doc`) | `Doc (Path × Role)`, `Stream` | the positioned printer and the layout | R2; `Doc` first pass |
| `inspect` (over any `Sig`) | handles, children, windows | the generic lenses the inspection protocol serves | `NodeLenses` generated for `Eff` |

An **AST transform** is an instance whose carrier is a term type: `Algebra(Sig, Term(Sig'))`.
`weaken` and `expandRound` are transforms `Eff → Eff`; `print` is a transform `Eff → Tree`;
`render` is `Tree → Doc`; the schema printer is `Representation → Tree`. So the owner's
"meta language spoken in schemas and AST transforms" has exactly this grammar: a schema per
signature, an algebra per transform, `fold` to apply, `Hom` to compose (fusion says
`fold alg' ∘ fold algToTerms = fold (alg' ∘ algToTerms)`, which is why two-stage pipelines
cost one traversal). Nothing else is needed, and nothing else should be added until a
consumer asks for it. That is the simplicity rule in one sentence.

## 2. The medium: jumping between Effect and static data

```
        Build (typed client, authoring lifts)              fold run
 host code ───────────────────────────────► Term (data) ──────────────► Effect<A, E, R>
      ▲                                       │  ▲                          │
      │ read (R5/R6: text in the image)       │  │ decode / toJson / wire     │ tape (truth harness)
      │                                       ▼  │                          ▼
 TypeScript text ◄──── print (fold) ────── store (P6, digests) ◄──── machine (Lean, OCaml)
```

A program is Effect when it runs and data when it is stored, inspected, typed, proved,
diffed or shown to a model. The two are related by `run` being a fold, and the claim that
the fold agrees with the machine is the existing lane: the truth harness already records
tapes of printed programs under the Effect runtime and compares them with the machine, so
`run` joins that lane as a second host route beside the printed text (R0's agreement lane
stays for `tsgo`). The store is the memo table and the identity: a term's digest includes
the pins, so a result is addressable and replayable.

The inspection protocol (layout note §4.14b) is the generic part of this picture served
over MCP: `resolve`, `at`, `children` are `Build`'s inverse lenses; `render` and `window`
are folds; `evaluate` is `run` on a term over the inspection rows. The server is an Effect
program on bun generated from the `InspectOp` signature through the same five words (its
`Schema` is the message set pinned to rc.112's `McpSchema`, its instances the handlers).

## 3. The TypeScript form, concretely

What the generator emits per signature, with `Eff` as the example. `eff.gen.ts` exists; the
three new files follow its conventions (generated header, declaration order, work stack,
no hand edits, drift-checked by `make check-gen`).

```ts
// algebra.gen.ts (new)
export type EffFam = "eff" | "stmt" | "stmts" | "effs" | "action" | "layer" | "layers"
export interface EffAlgebra<R extends Record<EffFam, unknown>> {
  readonly eff_succeed: (value: Term) => R["eff"]
  readonly eff_suspend: (body: R["eff"]) => R["eff"]
  readonly eff_perform: (op: NativeOp, request: Term) => R["eff"]
  readonly eff_bind: (first: R["eff"], rest: R["eff"]) => R["eff"]
  readonly eff_gen: (body: R["stmts"]) => R["eff"]
  readonly eff_provideLayer: (layer: R["layer"], isLocal: boolean, body: R["eff"]) => R["eff"]
  // … one field per constructor of every family, names verbatim from Fold.lean:940
  readonly stmts_nil: R["stmts"]
  readonly stmts_cons: (head: R["stmt"], tail: R["stmts"]) => R["stmts"]
}
export const fold: <R extends Record<EffFam, unknown>>(alg: EffAlgebra<R>) => (e: Eff) => R["eff"]
// generated with an explicit work stack, as wire.gen.ts is, so deep programs do not
// consume the JavaScript call stack; one fold per family (foldStmt, foldLayer, …)

// build.gen.ts (new): the constructors as a typed API, the same names as the Lean lifts
export const Eff = {
  succeed: (value: Term): Eff => ({ _tag: "succeed", value }),
  bind: (first: Eff, rest: Eff): Eff => ({ _tag: "bind", first, rest }),
  // …
} as const

// hom.test.ts (new, generated): the laws as corpus guards
// fold(idAlgebra)(e) deep-equals e on every corpus program; fold(alg') ∘ fold(toTerms)
// equals fold(fused) where the Lean side proves cata_eff_fusion
```

Two facts decide that TypeScript is the natural host for the algebra form. First, the
family-indexed carrier `R["eff"]` is an indexed access type, native to TypeScript, which is
exactly the parameter the LCNF-to-OCaml emitter refuses (`EffAlgebra: unsupported parameter R
at 1`); OCaml needs the uniform-representation rule (layout note §4.15) for the same
construct. Second, an instance is an object literal, which is how Effect's own folds are
written (`SchemaAST` transformations, `Schema.toJsonSchema`, `toArbitrary`), so generated
instances read as idiomatic Effect code and hand-written ones look the same.

The `run` instance, in that form, is the medium's first payload:

```ts
// run.ts: the AST compiler that can run; hand-written in the algebra form first
export const runAlgebra: EffAlgebra<{
  eff: Effect.Effect<unknown, unknown, never>
  stmt: …; stmts: …; effs: …; action: …; layer: Layer.Layer<never>; layers: …
}> = {
  eff_succeed: (value) => Effect.succeed(evalTerm(value)),
  eff_bind: (first, rest) => Effect.flatMap(first, () => rest),   // answers are de Bruijn: the env is threaded, see §8 Q-B
  eff_perform: (op, request) => nativeRow(op)(evalTerm(request)),
  // …
}
export const run = fold(runAlgebra)
```

## 4. How much comes in this form, and from where

**The census at the top level is already known.** Every function over `Eff` that a new
constructor costs (the state file's "hand-written owners": `effTy`, `compileEff`, `denote`,
`print`, `read`, `Straight`) is fold-shaped: four are folds with one parameter (`effTy` with
the environment, `compileEff` with the point, `denote` with the value environment, `print`
with the depth), which is an algebra with the exponential carrier `P → X`; `Straight` is a
plain fold into `Bool`; `read` is a fold over the other signature (`Tree`). Five modules
outside `Fold.lean` already use the generated algebra, and the universal-algebra refactor
moved `weaken`, `expandRound`, `refSites`, `layerPaths` through it. Twenty-seven files use
`termination_by`; those are the machine (`step`, `run`, the scheduler), the authoring
elaboration and the readers' loops, which are not transforms of a term and stay ordinary
functions on every host.

So the classes are, and a census tool assigns every definition reachable from the API roots
to one of them:

| class | shape | emitted as | expected members |
| --- | --- | --- | --- |
| D | an inductive | `Schema(Sig)` | the 28 families of `Eff`, `Tree`, `Doc`, `Representation`, `InspectOp`, the MCP messages |
| C | structural recursion whose recursive calls are only on direct children with unchanged parameters | `fold(alg)` with `alg`'s cases read off the equation lemmas | `Straight`, `weaken`, the codecs, `render`, `layout`, `measure` |
| P | as C with a parameter that changes along the recursion (environment, depth, point) | `fold(alg)` at the exponential carrier | `effTy`, `explain`, `compileEff`, `denote`, `print` |
| M | a `foldM` shape (the generated monadic fold: children run in declaration order, no short-circuit) | `fold` into `Effect` | the compile plan's execution, `run` |
| G | fuel, `partial`, non-structural, or state machines | an ordinary function, from LCNF as `api_gen.ml` does for OCaml | the machine, elaboration, the reader's tie-break loops |
| X | builtins the host provides | the builtin rows (about ten) | string operations, hashing, the store |

**Where the bodies come from.** Two sources exist for a C or P case body. The equation
lemmas (`f.eq_n`) are at the Lean term level with names and one equation per constructor,
which is the algebra instance verbatim: `effTy_eq_bind : effTy sig env (bind a b) = …` is the
`eff_bind` field. LCNF is after ANF conversion, closure conversion and erasure: complete,
already targeted by `LcnfGen`, and unreadable as Effect code. The recommendation is to read
the C and P classes off the equation lemmas (a new emitter in `Tools`, small: it walks
`Expr`, refuses anything it does not recognise, and refuses loudly) and to keep LCNF for the
G class, where readability does not matter and completeness does. "How much can we generate
from LCNF" then has a precise answer per class: D, C and P are generated from the signature
and the equations, M and G from LCNF, X is the builtin table; the census tool prints the
counts, and the owner reads a number, not a hope.

## 5. The entire Effect surface, ingested once, as types with a schema input and output

The owner's standing requirement, restated tonight: ingest the entire Effect API surface for
codegen and have it representable as types, where each entry "is a type with a schema input
and output". Not one module at a time, not one model per module, and no semantics in Lean
("they don't; we just render them as TypeScript, like we would Mailbox or EventLog").

**The entry.** Every export of the pinned package becomes one value of one shape:

```
Entry := { module, name, typeParams : List Name,
           input  : Schema,            -- the parameters, as one schema (a struct)
           output : Schema,            -- the result; for an Effect: answer, error, requires
           cite : String }             -- the declaration's location and doc comment
```

A schema is a P2 document (`Representation`), with what the surface needs and the model
already half has: type-constructor application with parameters (`Effect<A, E, R>`,
`Queue<A, E>`, `Stream<A, E, R>`), function-typed parameters as an entry one level down
(`input → output` again, which is what a hole under a binder is), and type parameters as
holes filled at use sites (a schema with holes is a template, the same object as §1's
`Build`). This is the shape Effect itself uses for everything it exposes over a boundary
(`HttpApi` endpoints, `AiToolkit` tools, `Rpc` definitions: a payload schema and a success
schema) and the shape of R12's tool table, so there is one entry type for the library
surface, the tool surface and the inspection protocol, and one emitter family over it.

**The mechanism, R8 pulled forward as the medium's first foreign signature.**

1. **Import.** `tsgo`'s AST API reads every declaration of `vendor/effect-4.0.0-rc.112/src`
   (the modules and `unstable/*`) into entries: names, type parameters, parameter and return
   types, doc comments. The same importer that reads the syntax table (R2); the type nodes
   are kinds of that table, so the type syntax is already imported data. Nothing is typed by
   hand, and the two hand-written packages (`SqliteBun`, `KeyValueStoreMemory`) are
   regenerated from their entries and must come out byte-identical: that is the guard.
2. **Classify.** A fold over the entries into rows, forms and refusals: a first-order input
   and output is a row (`Row`'s request, answer, error and requirements are projections of
   the two schemas; sync, async or program by the output's shape); a function-typed input is
   a form (a template with holes, the closure the owner asked holes for); anything beyond
   the forms is refused with a listed reason. The classification is itself a document in
   the store, and the census over it (entries, rows, forms, refusals, per module) is the
   number that says how much of Effect a program can use.
3. **Represent in `Ty`.** `Ty` stays the core language's projection of types and gains
   type-constructor application, `Ty.app name args`, of which `Ty.handle target` is the
   nullary case; the surface document supplies the constructors and their arities.
   Assignability between foreign constructors is the host checker's verdict (O17, R0's
   lane), external evidence by design, never re-implemented in Lean.
4. **Render, do not model.** A row prints as the host call its spelling names, runs on the
   Effect runtime, and is answered by the tape on replay (`NativeOp.external`, the recorder
   tape, exactly as the two packages today). Lean holds typing, spelling and citation,
   nothing else. The lanes: R0 for every printed row under `tsgo` (a row TypeScript refuses
   is an import defect), the tape schema for answers on replay.

**Later, a reification, and what it would cost.** rc.112's own structure (read from the
source tonight): `Channel` is an `Effect` producing a `Pull`, `Stream` wraps a `Channel`,
`Pull` is an `Effect` that yields an element or halts with the done value, and `Queue`
implements `take` and `offer`. So when the owner wants "our own reification of these
semantics", it is one store (the queue: a buffer, its strategy, parked takers and offerers,
`end` and `done`) and one row (`pull`), with every other module's meaning derived as a
program over them by the fold that already gives programs their meaning. That is cheap
because everything reduces to `pull`, and it is not now.

## 6. What exists and what is missing, per host

| piece | Lean | TypeScript | OCaml |
| --- | --- | --- | --- |
| the signature as data | read off the environment (`World`) each run | consumed through `TsGen` | consumed through `EffGen` |
| `Schema` | inductives | `eff.gen.ts` | `eff_types.ml` |
| `Algebra`, `fold` | generated (`Fold.lean`) | **missing** | **missing** (uniform representation needed) |
| `Hom` | generated except fusion for `Eff` | **missing** (corpus guards) | **missing** |
| `Build` | the authoring lifts | **missing** (the typed client) | constructors |
| codecs | `Wire`, `Canonical` | `json.gen.ts`, `wire.gen.ts` | `eff_json.ml`, `eff_wire.ml` |
| `run` | the machine | **missing** | the engine |
| `print`, `read` | hand-written; R4, R5 | `read.ts` hand-written; R6 | **missing**; the template table's emitter |
| the surface as entries (input schema, output schema) | two packages by hand; the importer missing | `packages.gen.ts` projected | projected |
| the inspection server | none | **missing**: generated Effect MCP on bun | serves the same protocol document |

## 7. The order, simple first

1. **Persist the signature.** `World` becomes a pinned document (`generated/sig/eff.json`,
   the one-generator plan's last step moved first), generated from the environment and
   drift-checked; `TsGen`, `EffGen` and the `Effect4Gen` generators read it. One input for
   every generator, inspectable through the protocol like any document.
2. **Emit `algebra.gen.ts`, `build.gen.ts`, `hom.test.ts`** from that document, in the
   conventions of `wire.gen.ts`. Small, additive, the corpus is the guard.
3. **The `run` instance**, hand-written in the algebra form, joined to the truth harness's
   tape lane; this is the medium's proof of life and `evaluate`'s engine.
4. **The census tool** (`Tools`, Lean): every definition reachable from the API roots
   classified D, C, P, M, G, X; a table in `generated/`; the counts are the answer to "how
   much".
5. **The equation-lemma emitter** for C and P, starting with `Straight` and `effTy`, so the
   host types programs without Lean in the loop; then `explain` as its projection.
6. **The same five emitters for the next signatures**: `InspectOp` (the MCP server on bun),
   `Tree` and `Doc` (R2), and the entire Effect surface as entries (§5), rows and forms
   derived, the two packages regenerated byte-identical as the guard.
7. **`cata_eff_fusion` and `AlgMap`** in the Lean generator, so two-stage pipelines are one
   traversal by theorem and the naturality of the compile plan (layout note §4.12) is
   statable.

Steps 1 to 3 are days, not weeks; nothing in them touches an alphabet or a proof.

## 8. Questions to workshop

Each question in plain words: what is being decided, what the two ways look like on a real
example, the recommendation, and what it costs.

### Q-A. Where does the generator's input live?

**The decision.** Every generator needs the list of families, constructors and fields (the
signature). Today each generator reads it off the Lean environment at run time
(`OCaml5.Eff.World.readBlocks`), so nothing can be generated without a Lean build, and
nobody can look at the signature as a thing. The alternative is to write the signature out
once as a document and have every generator read that file.

**What it looks like.** A file `generated/sig/eff.json`, written by one Lean tool, one
entry per constructor, in declaration order:

```json
{ "families": [
  { "name": "Eff", "kind": "union", "constructors": [
    { "name": "succeed", "fields": [ { "name": "value", "carrier": "Term" } ] },
    { "name": "bind",    "fields": [ { "name": "first", "carrier": "Eff" },
                                     { "name": "rest",  "carrier": "Eff" } ] },
    { "name": "gen",     "fields": [ { "name": "body",  "carrier": "Stmts" } ] } ] },
  { "name": "Stmts", "kind": "list", "element": "Stmt" } ] }
```

`TsGen`, `EffGen` and the `Effect4Gen` generators read this file instead of the
environment. A guard rebuilds it from the environment and fails if the two differ, the
same drift check every generated file already has (`make check-gen`).

**Recommendation.** The document. Three reasons: the TypeScript and OCaml generators can
run on any machine without Lean; the signature becomes inspectable through the protocol
like any other document; and there is exactly one input for every generator, so a new
constructor is one edit in Lean and one regenerated file, never a hunt through tools.

**Cost.** One small Lean tool that writes the file, one guard, and a one-line change in
each generator to read it. A day.

### Q-B. How does the host `run` instance handle variables?

**The decision.** In `Eff`, the result of one step is not named. `bind(first, rest)` means
"run `first`, then run `rest` with the result available as variable 0"; a variable is a
number counting back through the binds (de Bruijn). So an instance that runs a program on
the Effect runtime has to keep an environment of earlier results. Two ways: thread an
environment explicitly, exactly as the Lean meaning `denote` does (`denote : NativeEff →
List Val → …`), or try to use JavaScript closures so that the code reads like ordinary
Effect.

**What it looks like.** The program "let x = 3; return x" is data:

```ts
const p: Eff = { _tag: "bind",
  first: { _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 3 } } },
  rest:  { _tag: "succeed", value: { _tag: "var", index: 0 } } }
```

With an environment the carrier is a function of the environment, and `bind` extends it:

```ts
type Run = { eff: (env: ReadonlyArray<Val>) => Effect.Effect<Val, Failure>, /* other families */ }
const runAlgebra: EffAlgebra<Run> = {
  eff_succeed: (value) => (env) => Effect.succeed(evalTerm(value, env)),
  eff_bind: (first, rest) => (env) =>
    Effect.flatMap(first(env), (v) => rest([v, ...env])),   // variable 0 is now v
  eff_perform: (op, request) => (env) => nativeRow(op)(evalTerm(request, env)),
  // one case per constructor
}
export const run = (p: Eff) => fold(runAlgebra)(p)([])
```

The closure version cannot exist as a fold: `rest` is data that says `var 0`, not a
JavaScript function that could close over `v`. Closures only appear when the program is
printed as TypeScript text, and that is the printer, not the runner.

**Recommendation.** The environment, as `denote` has it. Then the tape lane compares like
with like: the Lean meaning, the OCaml engine and the host runner all thread the same
list, and a disagreement points at one constructor's case.

**Cost.** Nothing beyond the instance itself; the shape is forced by the data.

### Q-C. Where do the case bodies come from when we generate instances from Lean?

**The decision.** A Lean function like `Straight` (is this program in the straight
fragment?) is a fold: one case per constructor. We can generate the TypeScript instance
either from the function's equation lemmas (Lean produces `Straight.eq_1`, `eq_2`, … one
equation per constructor, at the level of named Lean terms) or from LCNF (the compiler's
intermediate form after ANF conversion, closure conversion and type erasure, which the
OCaml path already consumes).

**What it looks like.** From the equations, the instance is readable and looks like what a
person would write:

```ts
export const straightAlgebra: EffAlgebra<{ eff: boolean; stmt: boolean; stmts: boolean; effs: boolean; action: boolean; layer: boolean; layers: boolean }> = {
  eff_succeed:   (_value)                 => true,
  eff_bind:      (first, rest)            => first && rest,
  eff_perform:   (op, _request)           => isSync(op),
  eff_whileLoop: (_init, _test, _step, _b) => false,
  // …
}
export const straight = fold(straightAlgebra)
```

From LCNF it comes out the way `ocaml/gen/api_gen.ml` does today: one big recursive
function with numbered temporaries, complete, correct, and not something anyone reads or
extends. The equation route needs a small recogniser: a case body must be built from the
children's results, the non-recursive fields, and calls to known functions; anything else
is refused with a message naming the definition and the equation, and that definition
stays on the LCNF route.

**Recommendation.** Equations for the fold-shaped definitions (the structural ones and
the ones with a parameter such as `effTy`'s environment), LCNF for the general ones (the
machine, the scheduler). The census tool prints how many definitions land on each route,
so the choice is measured, not guessed.

**Cost.** The recogniser and emitter, a few hundred lines of Lean in `Tools`, and the
census tool beside it.

### Q-D. Which instances first on the host?

**The decision.** The order in which generated instances arrive in TypeScript. The
candidates are `run` (execute a program as data), `Straight` (the fragment predicate),
`effTy` (the typing) with `explain` (why a program is refused), and `print`.

**What it looks like.** `effTy` is a fold with an environment of types, so its instance has
the same shape as `run`:

```ts
type Typing = { eff: (env: TyEnv) => EffTy | null, /* … */ }
const typingAlgebra: EffAlgebra<Typing> = {
  eff_succeed: (value) => (env) => ({ answer: termTy(value, env), error: NEVER, requires: [] }),
  eff_bind: (first, rest) => (env) => {
    const a = first(env); if (a === null) return null
    const b = rest(extend(env, a.answer)); if (b === null) return null
    return { answer: b.answer, error: union(a.error, b.error), requires: merge(a.requires, b.requires) }
  },
  // …
}
```

With that in the host, the inspection server answers `explain` without Lean in the loop,
and the answer agrees with Lean by the tape lane. `print` is not on this list because the
template table (R4) makes it rows; generating it twice would be waste.

**Recommendation.** `run` first (the medium's proof of life, and what `evaluate` runs),
then `effTy` and `explain` from the equations, then `Straight` because it is the smallest
and a good first test of the emitter.

**Cost.** `run` is written by hand in the algebra form; the other three come from Q-C's
emitter.

### Q-E. How big is the generated TypeScript surface?

**The decision.** Per signature the generator can emit exactly five things (the schema of
terms, the algebra type, `fold`, the law guards, the builder) and nothing else, or it can
also emit conveniences (mapping, traversals, pattern helpers).

**What it looks like.** A user file with the five names and nothing more:

```ts
import { Eff, EffAlgebra, fold, Build } from "./eff"        // Schema types, Algebra, fold, Build
const performs: EffAlgebra<{ eff: number; stmt: number; stmts: number; effs: number; action: number; layer: number; layers: number }> = {
  eff_perform: () => 1, eff_bind: (a, b) => a + b, eff_succeed: () => 0, /* … */
}
const p = Build.Eff.bind(Build.Eff.succeed(lit(3)), Build.Eff.succeed(v(0)))
fold(performs)(p)   // 0
```

Everything a user might want beyond that is an instance written in the same shape, and
the law guards (`fold(id)` is the identity on every corpus program) are generated tests.

**Recommendation.** Five names, no combinator library. The moment a second consumer wants
the same helper, it becomes a generated instance, not a hand-written utility.

**Cost.** None; this is the cheaper option.

### Q-F. What happens to surface entries the forms cannot express?

**The decision.** When the entire Effect surface is ingested as entries (input schema,
output schema), some entries have function-typed inputs. The forms (templates with holes)
cover some of those shapes today. Either refuse what the forms cannot express, list the
refusals, and grow the forms against that list; or grow the forms first.

**What it looks like.** Three entries from rc.112 and their fate:

```
Queue.offer(self: Enqueue<A, E>, message: A): Effect<boolean>
  → a row: input { self: handle Queue<A,E>, message: A }, output Effect<boolean>
Stream.map(self: Stream<A, E, R>, f: (a: A) => B): Stream<B, E, R>
  → a form: one lambda with a first-order body; the hole is the closure
Effect.callback(register: (resume: (effect: Effect<A, E>) => void) => void)
  → refused: a function that takes a function; reason listed with the citation
```

The census over all entries prints, per module: entries, rows, forms, refused. The refusal
list is then the specification for the forms' next step, with real counts behind it.

**Recommendation.** Refuse and list first; grow the forms second. Growing first means
designing holes for shapes nobody has counted.

**Cost.** The classifier is one fold over the entries; the census is a table it writes.

### Q-G. What runs the inspection server?

**The decision.** The inspection protocol is served over MCP. It can be generated Effect
TypeScript (rc.112's `McpServer`, `Tool`, `Toolkit`) running on bun over stdio, with one
detail: the `check` command needs `tsgo`, whose JavaScript client only runs under node, so
`check` spawns node for that one call.

**What it looks like.** One generated tool per command, every success an object (MCP
publishes an output schema only for object-typed successes, `McpServer.ts:1535`):

```ts
const Explain = Tool.make("explain", {
  parameters: Schema.Struct({ program: EffSchema }),
  success: Schema.Struct({ refusal: Schema.NullOr(TypeRefusalSchema), codes: Schema.Array(Schema.Number) })
})
const Window = Tool.make("window", {
  parameters: Schema.Struct({ handle: Digest, offset: Schema.Number, lines: Schema.Number, width: Schema.Number }),
  success: Schema.Struct({ text: Schema.String, spans: Schema.Array(SpanSchema) })
})
const server = McpServer.layerStdio({ name: "effect4", version: PROFILE_STAMP, toolkit: Toolkit.make(Explain, Window, /* … */) })
```

`explain` calls the generated typing instance of Q-D; `window` calls the layout fold; the
handlers are instances, the server is the signature's emitter.

**Recommendation.** Yes: generated, on bun, node only for `tsgo`.

**Cost.** The emitter over the inspection signature, and the profile stamp on the
initialize response so a client refuses a mismatched grammar.
