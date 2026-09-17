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

## 5. The whole Effect through the same construct

Queue, PubSub and the rest of the module surface (rc.112 ships `Queue.ts` with 35 exports,
`PubSub.ts` with 26, and `Channel`, `Stream`, `Sink`, `Schedule`, `Semaphore`, `Latch`, the
`Tx*` variants) have no Lean representation today; `Mailbox` is v3's name for what rc.112
calls `Queue` with `end` and `done`. The mechanism they use exists: a package is a service
with a key, a module path, a service type code, a handle target and a `RowTable`
(`Program/Packages.lean`; `SqliteBun` and `KeyValueStoreMemory` are the two), and a row is
data (`Row`: name, spelling, shape, kind sync/async/program, request, answer, error,
requires, cite, type arguments, registration), printed by its spelling, read by the
generated row answer, typed by `effTy`, answered by the machine or the tape.

Through the medium this is one more signature import and one row table per module, with
the host runtime as the semantics:

1. **The module surface as a document (R8).** `tsgo`'s API reads `Queue.ts`'s declarations
   from the pinned package (names, type parameters, parameter and return types) into a P2
   document; the same importer that reads the syntax table. Nothing is typed by hand.
2. **Classification, decided per export.** A value-returning function of first-order
   arguments is a sync row; one returning `Effect` that may suspend (`take`, `offer` on a
   bounded queue) is an async row; one whose argument is a function (`Queue.make` with a
   strategy is data, but `PubSub.subscribe` returns a scoped `Queue`) is a program row or a
   form; anything higher-order beyond the forms is refused with its reason listed. The
   classification is a fold over the surface document into `Option Row`.
3. **No machine semantics in Lean.** The owner's ruling, same night: "they don't; we just
   render them as TypeScript, like we would Mailbox or EventLog." A queue or pubsub row is
   rendered as the host call its spelling names, executed by the Effect runtime, and
   answered by the tape on replay: the external-row mechanism (`NativeOp.external`, the
   recorder tape) the two existing packages already use. The machine's semantics of such a
   row is the tape; Lean holds its typing (request, answer, error, requirements from the
   surface document), its spelling, and nothing else. No store, no strategy model, no
   coverage witnesses.
4. **The lanes.** R0 for the printed rows under `tsgo` (a row that TypeScript refuses is a
   surface-import defect); the recorder tape's schema for the row's answers on replay.

The order inside this: `Queue` first (it is what `Mailbox` became, and `Stream` and
`Channel` are built on it), `PubSub` second, then `Semaphore` and `Latch` (small stores),
then `Schedule` (data, no store), then `Stream`, `Sink` and `Channel`, which are the large
ones and whose higher-order operations decide how far the forms must grow.

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
| the module surface | two packages by hand | `packages.gen.ts` projected | projected |
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
   `Tree` and `Doc` (R2), the module surface (§5, `Queue` first).
7. **`cata_eff_fusion` and `AlgMap`** in the Lean generator, so two-stage pipelines are one
   traversal by theorem and the naturality of the compile plan (layout note §4.12) is
   statable.

Steps 1 to 3 are days, not weeks; nothing in them touches an alphabet or a proof.

## 8. Questions to workshop

**Q-A, the starting schema.** Is the signature the Lean environment (today) or a persisted
document the environment is checked against, so that the TypeScript and OCaml generators
run without Lean and the document is itself inspectable? Recommended: the document, with
the drift check every generated file already has.

**Q-B, the `run` instance's answers.** `Eff.bind`'s answer is a de Bruijn variable, so the
run algebra threads an environment: the exponential carrier `Env → Effect`, as `denote` has
it. Take that (one parameter, the same shape as `denote`, so the tape lane compares like
with like), or a host-native encoding with JavaScript closures, which reads better and
proves nothing? Recommended: the environment, as `denote`.

**Q-C, where C and P bodies come from.** The equation lemmas (readable instances, a small
new emitter that refuses what it does not recognise) for C and P, LCNF for G? Or LCNF for
everything, accepting unreadable instances? Recommended: equation lemmas for C and P, LCNF
for G, the census decides the counts.

**Q-D, the first instances on the host.** `run` first, then `Straight` and `effTy` from the
equations, then `explain`? Or `print` first (which R4 makes rows anyway)? Recommended:
`run`, `effTy`, `explain`; `print` arrives as the template table.

**Q-E, the surface of the generated TypeScript.** Exactly five names per signature
(`Schema`, `Algebra`, `fold`, `Hom` guards, `Build`), everything else an instance a user
writes or a generator emits in the same form? Recommended: yes; no combinator library on
top until a consumer needs one.

**Q-F, the module surface's order and depth.** `Queue` first, then `PubSub`, `Semaphore`,
`Latch`, `Schedule`, then `Stream`, `Sink`, `Channel`; refuse higher-order operations
beyond the forms with a listed reason rather than growing the forms first? Recommended:
that order and that rule; the refusal list is the design input for the forms' next step.

**Q-G, the bun server.** The inspection server as generated Effect TypeScript over the
`InspectOp` signature on bun, with `check` shelling to node for `tsgo` (bun cannot host the
native client's sync pipe)? Recommended: yes.
