# The AST relation: Effect TS programs as Lean data, in both directions

Date: 2026-09-04. Status: v1, grilled against the sources named below; open
decisions in §9. Ruling it rests on: `docs/research/2026-09-04-cleanup-inventory.md`
§5″ — the DSL stays as the fine formalisation of the Effect TS surface, the
native route is added beside it, and Deep is the model under both.

## 0. What "the relation" is

One first-order AST, `Eff`, that is *the syntax of the Effect TS programs we
emit and read*, sitting between the portable layer and the frame machine:

```
 Effect TS text  ⇄  Eff  →  Prim ν σ … + PrimInterp  →  Deep machine (RunMachine / FrameFiber)
   print/parse        compile (defunctionalise)              drive / run
                       ↑
        flows (Effects.Flow) and family scripts (the DSL)  →  Eff        front-ends
```

Four relations, each a theorem or a named receipt:

| relation | kind | statement |
| --- | --- | --- |
| R1 print/parse | theorems | `parse (print e) = some e`; `parse s = some e → print e = s` (the parser accepts exactly the printer's image) |
| R2 compile | theorems | the run of `compile e` by the frame machine equals the direct evaluator of `e`, fuel-exact (S4's `closeWalk` shape; foldlab's `runP_embed_agree` shape); the compile never reaches `notImplemented` on a well-typed `e` (progress) |
| R3 front-ends | theorems | `compileRegion flow = compile (ofFlow flow)` up to the name bijection; a family script is `ofScript`, and the service route prints it as it prints today |
| R4 host | receipt | rc.112 running `print e` under its run-loop hook at the same decision tape produces the frame stream the machine produces for `compile e`, under a named mask; outcome equal (traces phase) |

"Clean" means: `Eff` has decidable equality and no Lean function inside it;
the `PrimInterp` the compile needs is *derived from the AST* (the table is
the AST, `docs/FRAMES-DAG.md` separation 4), never hand-written; and every
constructor names the rc.112 primitive it compiles to and the public
combinator it prints as, by line.

## 1. Start from what exists — the inventory (read first, reuse second)

The user's instruction: begin from all related code for creating and parsing
code across this repo, foldlab, and the other Lean projects. Measured on
disk on 2026-09-04.

### 1.1 In this repository

| what | where | reuse |
| --- | --- | --- |
| TypeScript syntax and fixed-layout renderer | lean4-typescript `TypeScript/Syntax.lean` (224: `Expr`, `Stmt` with `constYield`, `yieldDiscard`, `ifElse`, `whileTrue`, `labelled`/`breakTo`/`continueTo`, `scopedGen`, `scopedGenMasked`; `ConstDecl`, `ProgDecl`, `ClassDecl`), `Render.lean` (307), `Structure.lean` (167: block graph → structured control by dominators), `Identifier.lean`, `HostPin.lean` | **the printer target, as is**; no parser exists there |
| the Effect v4 profile | `Effect4/Target/TypeScript/EffectV4.lean` (687: `Spelling` type profile with `render`/`depth`/`wireDefault`, `PureTerm`, `ServiceRow`/`Script`, `Lowering.callOf`/`performCall`/`nullaryValue`) | `Spelling` and `PureTerm` are the AST's type and expression sublanguages |
| script → flow embedding | `ScriptFlow.lean` (257: `OpSpec`, `OpKind`, `tableAlphabet`) | the family front-end `ofScript` is this embedding followed by `ofFlow` |
| control IR and its printer | `Skeleton.lean` (508) + `SkeletonRender.lean` (172); `FlowLower`/`RegionLower`/`StructuredLower` | the service-route printer stays; the native printer reuses `SkeletonRender`'s call builders |
| fiber profile and its lowering note | `FiberProfile.lean` (348), `Effect4/Deep/fork-lowering.md` | the fork rows' spellings and the roots convention |
| the flow → frames compile and its agreement | `Effect4/Semantics/RegionSimulation.lean` (`Config`, `RegionName`, `compileRegion`, `closeWalk`, `leaveConfig_agrees_runRegions`) | the *naming pattern* (`cont (point : Config)`) and the *proof pattern* (the walk is the runner) transfer verbatim |
| the native alphabet, already first-order | `Effect4/Deep/Stores.lean` (`Val`, `SyncOp`, `ProgName`, `Name`, `ActionName`, `Thunk`, `Program := Prim Name Thunk Val Err Defect FiberId Ann`) | `ProgName`/`ActionName` are an `Eff` fragment in all but name: absorbed, not duplicated |
| classification of profile ops | `Effect4/Deep/ForkFlow.lean` (`fiberPrim`, `parkOf`, `catchesMachineFailure`) | the compile's fork arms |
| the DSL elaborators | `Effect4/Meta/Derive.lean` (494: `effect_signature`, `effect_program`, `effect_atoms`, `spellingOfType`) | unchanged; gains the native lowering mode |
| host side | `harness/trace/tracer.ts` (`TapeScheduler`, `registerHandle`, the wire decoder), `harness/trace/patched/` (seven observation hunks), rc.112's `currentTracerContext` hook (`internal/effect.ts:653-655`) | R4's instruments |
| JSON | `Effect4/Data/Json.lean` (520: binary64 datum and raw JSON tree; no parser) | the value carrier for the decoder in §6 |

### 1.2 In foldlab (vendored pin under `vendor/foldlab/pinned/tree/library/cas`, and `C:\Users\kokok\Dev\foldlab`)

| what | where | reuse |
| --- | --- | --- |
| defunctionalised program table with the agreement theorem | `Cas/Lang/Defun.lean` (2,006): `PLine`/`PProg`, `embed` (higher-order) vs `runP` (direct) with `runP_embed_agree`; `encodeLine`/`decodeLine` with `decodeLine_exact`; `decodeProg_encodeProg` ("the program is content") | **the theorem set to copy for R2 and R1**: embed-vs-direct agreement, and encoder-image exactness |
| program emission through the same object the decoder answers | `Cas/Backend/EmitProg.lean` (125): `PProg → emitted text → recognized → decoded → PProg` as a round trip between named functions | the design of R1's two directions |
| the Effect-TS recognizer lane (the "lift") | `C:\Users\kokok\Dev\foldlab\archive\cas-program\lift-harness\src\` (`contract.ts` 10.6 KB, `lift.ts` 16.3 KB, `oxc-engine.mjs` 17.4 KB, `gate.ts`, `sieve.ts`); Lean side `Cas/Lift/Decode.lean` (761), `Taxonomy.lean` (241, the closed refusal taxonomy `E-PARAM-SHAPE` … `E-HELPER-UNPINNED`), `Manifest.lean` (207, one manifest both surfaces, interchange law R11) | **the parsing chassis for real Effect code**: two engines (oxc-parser 0.147.0 and the TypeScript compiler API 5.9.2) emit canonical JSON verdicts, an agreement gate compares them, Lean decodes the document into the table and refuses by code |
| strict canonical JSON parser with proofs | `Cas/Values/JsonParse.lean` (1,095): `parse : String → Option Value`, `parse_sound`, `parse_render` | the exactness style for R1's Lean-side parser, and a decoder input reader |
| TS fragment and printer, the ancestor | `Cas/Backend/Ts.lean` (220), `EmitAst.lean` (313, sharing-aware emission), `EmitLayer.lean` | lean4-typescript is this, renamed; nothing to port |
| CPS program of a term with correctness | `Cas/Lang/TreeProg.lean` (480: `progK`, `putTree_correct`) | the shape of `embed` |
| corpus and census | `foldlab/corpus/effect_codebases/*` (real Effect codebases); `foldlab/experiments/parser-census` (what TS declarations a labelled corpus contains, both engines); `experiments/entity-store-extract` (extractor over pinned Effect source, TS API + oxc, inventory JSON) and `entity-store-generate` (inventory → Lean text with pins) | trial corpus for the recognizer; the generator discipline |
| admitted tools | `foldlab/docs/lab-core/TOOLS.md` rows: TypeScript compiler API `typescript@5.9.2`; `oxc-parser@0.147.0`; `lean4-tree-sitter` (`predictable-machines/lean4-tree-sitter` v0.2.4 at Lean v4.32.0, clone at `foldlab/.reference/clones/`); ESTree spec pin | the external parsers, already pinned; tree-sitter needs a Lean 4.33.1 check before it is usable here |

### 1.3 Other Lean projects

| project | what | reuse |
| --- | --- | --- |
| lean4-effects (`.lake/packages/effects`) | `Flow/Block.lean` (`RawTerm`: `ret`/`jump`/`perform`/`choose`/`performCatch`/`branch`), `Flow/Raw.lean`, `Flow/Region.lean` (`enter`/`acquire`/`leave`), `Flow/Admission.lean` (2,320), `Algebra/Program.lean` (the higher-order carrier `Program`, `pure`/`vis`) | `ofFlow`'s domain; `Program` is the embed target for the Reynolds theorem |
| lean4-CAS (`C:\Users\kokok\Dev\lean4-CAS`) | `generator/AGENTS.md` (deterministic emission, manifests, byte-identical regeneration, generation contributes no proof), `formal/language` (`Sig`/`Prog`/`Lawful`) | the generator discipline, adopted as written |
| lean4-WHATWG-streams | `Whatwg/Streams/Target/TypeScript/{Decode,Render}.lean`, `Meta/Emit.lean` (stubs) | the second reification will consume the same printer and parser chassis; keep them reification-neutral where the AST is not (§8) |
| repl | `REPL/JSON.lean` | nothing beyond JSON handling |

The one gap across all of it: **no parser of TypeScript exists in Lean.**
Every reading of TypeScript so far ran on the TS side (oxc, the compiler API)
and crossed into Lean as canonical JSON. The plan keeps that split (§6) and
adds only the Lean parser of our own printed image (§5), which is provable.

## 2. The AST

`Eff` is parameterised by the perform alphabet `Op` (positions in a table of
`OpSpec` rows: a family's rows for the service route, the native rows of
`Deep.Stores.SyncOp`/`ActionName` for the native route) and is first-order
throughout: values are `PureTerm`s over `Val`, variables are positions in
the current environment (`Var := Nat`, the flows' convention: every node
passes its whole scope forward and an answer is appended), and every
continuation is a body with one more variable.

```lean
inductive Eff (Op : Type) where
  -- exits
  | succeed (value : PureTerm)                       -- Effect.succeed        → Prim.success
  | fail (error : PureTerm)                          -- Effect.fail           → Prim.failure (Cause.fail e)
  | failCause (cause : CauseTerm)                    -- Effect.failCause      → Prim.failure
  | yieldError (error : PureTerm)                    -- yield* new E()        → Prim.yieldableError
  -- thunks
  | sync (thunk : PureTerm)                          -- Effect.sync (:929)    → Prim.sync
  | suspend (body : Eff Op)                          -- Effect.suspend        → Prim.suspend (thunk names the body)
  | perform (op : Op) (request : PureTerm)           -- yield* svc.op(x) | the native call → Prim.sync / withFiber / async by the row's kind
  -- sequencing, two frame shapes on purpose (§2.1)
  | bind (first rest : Eff Op)                       -- Effect.flatMap        → Prim.onSuccess
  | gen (stmts : List (Stmt Op))                     -- Effect.gen            → Prim.iterator
  -- failure
  | catchCause (body handler : Eff Op)               -- Effect.catchCause     → Prim.onFailure
  | matchCause (body onValue onCause : Eff Op)       -- Effect.matchCauseEffect → Prim.onSuccessAndFailure
  | onExit (body finalizer : Eff Op)                 -- Effect.onExit (:4006) → Prim.onExit
  | exit (body : Eff Op)                             -- Effect.exit           → Prim.exitFrame
  -- masks
  | uninterruptible (body : Eff Op)                  -- Effect.uninterruptible → withFiber setInterruptible false + Prim.setInterruptible (:4312)
  | interruptible (body : Eff Op)                    -- Effect.interruptible
  -- control by value (E4-FLOW-CE-029: branch decided by value only)
  | branch (test : PureTerm) (thenB elseB : Eff Op)  -- if in a gen body       → decided at compile time from the env
  | whileLoop (test step : PureTerm) (body : Eff Op) -- Effect.whileLoop (:4628) → Prim.whileLoop
  -- scheduling and parking
  | yieldNow (priority : Nat)                        -- Effect.yieldNowWith (:982) → Prim.yieldNowWith
  | callback (register : Op) (onInterrupt : Option (Eff Op))  -- Effect.callback (:1109) → Prim.async (+ asyncFinalizer)
  -- fibers and scopes
  | withFiber (action : ActionTerm Op)               -- Effect.forkChild/forkIn/…, interrupt, awaitAll, raceAll (:1147) → Prim.withFiber
  | scoped (body : Eff Op)                           -- Effect.scoped         → the region frames compileRegion emits
  | acquireRelease (acquire release : Eff Op)        -- Effect.acquireRelease
  -- flows only: refused by the native printer, tape-answered by the compile
  | choose (site : DecisionId) (left right : Eff Op)
```

with `Stmt Op` the statement forms of a `gen` body (`constYield` binding an
answer, `yieldDiscard`, `ret`, `ifElse`, `whileTrue`/`break`), each holding
`Eff Op` operands. `CauseTerm` and `ActionTerm` are the first-order spellings
of a `Cause` and of a `WithFiberAction` (`Deep.Stores.ActionName` already is
one). `deriving DecidableEq`; the separation-4 gate (`example : DecidableEq
(Eff Op) := inferInstance`) is the first receipt.

### 2.1 Why `bind` and `gen` are both there

rc.112 runs a `flatMap` chain as `OnSuccess` frames and a `gen` body as one
`Iterator` primitive whose inline fold (`PrimInterp.iterNext`) runs pure steps
until the generator yields an effect. Printing every sequence as `gen` and
compiling every sequence to `onSuccess` would make R4 false at the frame
level even when outcomes agree. So the AST records which one the program is,
and the printer and the compile agree on it: `bind` prints as
`Effect.flatMap` and compiles to `onSuccess`; `gen` prints as
`Effect.gen(function* () { … })` and compiles to `iterator` with an
`iterNext` derived from the statement list. This is the single most
important fidelity decision in the design; it is what "native capability"
buys over the service wall.

### 2.2 Types

A type assignment `typeOf : Eff Op → Option (Spelling × Spelling × Requirement)`
— the answer spelling `A`, the error spelling `E` (both `EffectV4.Spelling`,
so the depth rule and the wire inhabitant come for free), and the
requirement row `R` as `Deep.Context.Requirement` (`Row.normalize` of the
keys the program performs against). Well-typed means `typeOf e = some _`.
Two receipts on it: **progress** (R2's second half — a well-typed program's
compile never reaches `PrimInterp.notImplemented`) and **the host type
receipt** (the printed module type-checks under `tsc`/`tsgo` at the pin, as
today's modules do). The TypeScript type parameters of `Effect<A, E, R>` are
exactly these three, printed by `Spelling.render` and the requirement's
service names.

## 3. The compile (defunctionalisation)

Names are addresses. A continuation name is the *path* to the continuation
body together with the environment it closes over, the pattern
`RegionSimulation.RegionName.cont (point : Config)` already uses:

```lean
structure Point where
  path : List Nat          -- the subterm the continuation is
  env  : Env               -- the values in scope there
  fuel : Nat               -- for loops and the direct evaluator's exactness
  tape : Tape              -- decisions left (flows' choose sites only)
deriving DecidableEq

inductive EffName | cont (p : Point) | caught (p : Point) | fin (region : Nat) (p : Point) | …
```

`compile : Eff Op → Point → Prim EffName EffThunk Val Err Defect FiberId Ann`
by structural recursion, and the table is a *function of the program*:

```lean
def interpOf (e : Eff Op) : PrimInterp EffName EffThunk … where
  contA := fun (.cont p) v => compile (subtermAt e p.path) { p with env := p.env ++ [v] }
  …
```

so "the table is the AST" is a definition, not a claim. `EffThunk` is
`Deep.Stores.Thunk` (park / act / op / body) extended by the pure thunk of a
`sync`. The `RunInterp` hooks (`parkOf`, `withFiberOf`, `syncState`,
`registerAsync`, `finalizerProgram`, …) are instantiated exactly as
`Deep.Stores`/`Deep.ForkFlow` instantiate them today; nothing in the machine
changes.

The direct evaluator `eval : Eff Op → Point → State → Outcome` is the
single-fiber reference, structural in `e` and fuelled; the agreement theorem
is R2. Fork, park and race arms are not evaluated by `eval` — they are
`withFiber` actions the machine performs — so R2 is stated for the
single-fiber fragment and the fork arms are correct by definition (the AST
says fork; the compile emits the action). This is the same fence S4 drew.

## 4. The front-ends

* `ofFlow : RegionFlow Ty → Eff Op` — blocks become `gen`/`bind` chains with
  positional environments (flows already are), `perform` and `performCatch`
  become `perform` under `bind`/`catchCause`, `branch` becomes `branch`,
  `choose` becomes `choose`, `enter`/`acquire`/`leave` become
  `scoped`/`acquireRelease`. R3's equation with `compileRegion` is the
  acceptance theorem; once it holds, `compileRegion` becomes
  `compile ∘ ofFlow` and S4's agreement lemma is restated once for it
  (decision D3).
* `ofScript : Script → Eff Op` — through `ScriptFlow`'s embedding, so the
  service route is unchanged: the DSL's programs print as they print today.
* The native route is `Eff` written directly (or elaborated from a small
  surface syntax in `Meta/Derive.lean`, the DSL's native mode).

## 5. Printing, and the Lean-side parser (R1, our own image)

`print : Eff Op → TypeScript.Decl` into lean4-typescript's syntax, rendered
by `Render` under `house0`: deterministic, fixed layout, reserved identifiers
respected (`TypeScript.reservedIdentifiers`; the `awaitFiber` spelling stays).
Two styles are *syntax*, not options: `gen` prints as a generator body,
`bind` as a `flatMap` chain, per §2.1.

`parse : String → Option (Eff Op)` accepts exactly the image of `print`, in
`Cas.Values.JsonParse`'s manner: canonical spellings only, no forgiveness
(R6/R7 of foldlab's lift contract). Theorems `parse_print` and `parse_exact`.
This parser is small because the grammar is ours; it is the proven half of
"parsing code".

### 5.1 The spelling table (fixed 2026-09-04, checked against the census and `Effect.ts`)

`print : Signature → Nat → Eff Op → Except Refusal TypeScript.Expr`, the `Nat` the
environment's length, so the next binder is `a{n}`. Variables print as `a{i}`; literals as
`undefined`, the number, `true`/`false`, the quoted string; an atom as `atom(args)`. A row
prints by its `shape`: `spelling(request)`, `spelling()` on a unit request, or the value
`spelling` (the service route's nullary rows). Every name below is an rc.112 export
(`generated/stdlib-census.tsv`); `forkDaemon` and `Cause.merge` are not, so the table
says `forkDetach` and `Cause.combine`. lean4-typescript v0.5.0 supplies the three formers
the fragment lacked: `Expr.generator` (`function* () { … }`), `Expr.cond` (`t ? a : b`) and
`Expr.arrowBlock` (`(a) => { … }`).

| constructor | printed as |
| --- | --- |
| `succeed v` | `Effect.succeed(v)` |
| `fail e` / `failCause c` | `Effect.fail(e)` / `Effect.failCause(C)` with `C` = `Cause.fail(e)`, `Cause.die(d)`, `Cause.interrupt()` / `Cause.interrupt(who)`, `Cause.combine(l, r)` |
| `yieldError e` | `e` (a yieldable error is an Effect) |
| `sync t` / `suspend b` | `Effect.sync(() => t)` / `Effect.suspend(() => b)` |
| `perform op r` / `callback op r` | the row's shape |
| `bind first rest` | `Effect.flatMap(first, (a{n}) => rest)` |
| `gen body` | `Effect.gen(function* () { … })`; `bindYield e` → `const a{n} = yield* e`, `yieldDiscard e` → `yield* e`, `ret v` → `return v`, `ifElse`/`whileTrue`/`breakLoop` → the statements |
| `catchCause b h` | `Effect.catchCause(b, (a{n}) => h)` |
| `matchCause b v c` | `Effect.matchCauseEffect(b, { onFailure: (a{n}) => c, onSuccess: (a{n}) => v })` |
| `onExit b f` / `exit b` | `Effect.onExit(b, (a{n}) => f)` / `Effect.exit(b)` |
| `uninterruptible b` / `interruptible b` | `Effect.uninterruptible(b)` / `Effect.interruptible(b)` |
| `branch t a b` | `Effect.suspend(() => t ? a : b)` |
| `whileLoop i t s b` | `Effect.suspend(() => { let a{n} = i; return Effect.whileLoop({ while: () => t, body: () => b, step: (a{n+1}) => { a{n} = s } }) })` |
| `yieldNow p` | `Effect.yieldNowWith(p)` |
| `awaitFiber f joinEffect` / `awaitValue` | `Fiber.join(f)` / `Fiber.await(f)` |
| `fork p o` | `Effect.forkChild(p, O)` or `Effect.forkDetach(p, O)` when `o.daemon`, with `O` = `{ startImmediately: b, uninterruptible: true | false | "inherit" }` |
| `forkIn p o s` / `forkScoped p o` | `Effect.forkIn(p, s, O)` / `Effect.forkScoped(p, O)` |
| `runIn f s` | `Fiber.runIn(f, s)` |
| `interrupt f` / `interruptAll fs none` / `interruptAll fs (some who)` | `Fiber.interrupt(f)` / `Fiber.interruptAll(fs)` / `Fiber.interruptAllAs(fs, who)` |
| `awaitAll fs` | `Fiber.awaitAll(fs)` |
| `raceAll es` | `Effect.raceAll([e1, …])` |
| `getContext` / `getId` | `Effect.context()` / `Effect.fiberId` |
| `closeScope s e` | `Scope.close(s, e)` |
| `scoped b` / `acquireRelease a r` | `Effect.scoped(b)` / `Effect.acquireRelease(a, (a{n}, a{n+1}) => r)` |
| refused | `choose` (flows only); the internal actions `interruptScoped`, `awaitAllFailFast`, `snapshotChildren`, `awaitNewChildren`, `setContext` (no public spelling with the same frame shape) |

### 5.2 The parser is two layers, and the theorem lives at the tree (fixed 2026-09-04)

Every string function on this toolchain reaches `Classical.choice` (`String.toList`,
`foldl`, `toNat?`, the order; `Render.expr` through `escapeString`), so a theorem whose
proof unfolds a string function is outside the gate. R1 is therefore stated over the
fragment's tree, where `print` lands:

* `Effect4/Syntax/Read.lean`: `readEff : Signature → Nat → TypeScript.Expr → Except
  ReadRefusal (Eff Op)`, the inverse of `print` constructor by constructor (the `Nat` is the
  binder count, so `a{n}` is read back as `var n`; a row is recognised by its spelling and
  trailing names through a `Signature.opOfSpelling : String → Option Op`); `readStmts`
  over `List TypeScript.Stmt`; numbers in identifiers read from `String.toUTF8` bytes, never
  `String.toNat?`. Theorems `read_print : readEff sig n (print sig n e) = .ok e` (by
  structural induction over the mutual family, the printer's and reader's cases in step)
  and `read_exact : readEff sig n x = .ok e → print sig n e = .ok x` (the reader accepts
  exactly the printer's image). Both at `propext`/`Quot.sound`: the tree has no strings
  beyond identifier equality, which is choice-free.
* `TypeScript.Parse` (lean4-typescript, or `Effect4/Syntax/Lex.lean` until D5 is decided):
  bytes → `TypeScript.Expr` for the rendered fragment, deterministic, ASCII-only; its
  exactness against `Render` is a receipt admitted by exact declaration, like the three
  `StructureLaws` printer lemmas, because `Render` is on the wrong side of the string
  boundary (`Effect4/Target/TypeScript/SkeletonRender.lean`'s header).

`string → AST` is then `parseBytes ≫ readEff`; `AST → {IR, flow, atoms, prose}` is
`compile`, `ofFlow`'s inverse where one exists, `Term`'s atoms, and the arms table.

## 6. Reading real Effect code (the recognizer route)

For programs we did not print — the way to "control Effect in Lean" over an
existing codebase — the plan revives foldlab's lift chassis, retargeted at
`Eff`:

1. **Engines on the TS side**: oxc-parser and the TypeScript compiler API at
   their admitted pins (`TOOLS.md`), each `recognize(source) → Verdict[]`,
   verdicts as canonical JSON (`contract.ts`'s discipline: an Effect `Schema`
   is the contract, decoding validates and never repairs).
2. **Agreement gate**: two engines must answer canon-identical verdicts on
   the by-construction fixture corpus (`gate.ts`), and on
   `foldlab/corpus/effect_codebases` as the trial corpus.
3. **Lean decoder**: `decodeEff : Json → Except RefusalCode (Eff Op)` in
   `Cas.Lift.Decode`'s shape — its image is a declared sub-language, every
   form outside it is refused *by name* from a closed taxonomy
   (`E-ARG-CLOSURE` for a lambda with a body we cannot read, `E-OP-UNKNOWN`
   for a call outside the admitted API table, `E-BRANCH`/`E-LOOP` until the
   arms are attempted, `E-IMPORT-OPAQUE`, …), and `decode_exact` says a
   successful decode was an encoding. The API table is the rows with their
   rc.112 citations (§1.1), which is why the DSL's rows stay: they are the
   recognizer's admitted surface.
4. **Round trip as the gate** (foldlab `EmitProg` §): `Eff → print → recognize
   → decode → Eff` is an identity on the printed image, checked as a golden;
   on foreign code, decode-then-print-then-decode is idempotent.

lean4-tree-sitter is the candidate for moving step 1 into Lean later; it is
pinned at Lean v4.32.0 and must be re-checked at v4.33.1 before it is admitted
here. Not on the critical path.

## 7. The host relation (R4) — the traces phase, restated for `Eff`

`print e` is run by rc.112 at the same decision tape (`TapeScheduler`), the
run-loop hook records every primitive evaluated, the patched hunks record
pops, closes and memo builds; the machine's `RunEvent`/`FrameEvent` stream of
`compile e` is projected to the same alphabet; agreement under a named mask
plus outcome equality is the receipt. Object identity is first-seen order in
the hook. Internals with no public API remain unreachable from a printed
program. This section does not change; it now has an AST to be stated over.

## 8. What is Effect-specific and what is shared

`Eff` is Effect-specific by construction (its constructors are rc.112
primitives). Shared across reifications: lean4-typescript (syntax, renderer,
structure), the canonical-JSON reader, the recognizer chassis (engines,
verdict schema, agreement gate), and the decoder *pattern*. Decision D5 is
where the shared pieces live; the WHATWG reification's `Target/TypeScript/
{Decode,Render}.lean` stubs are the second consumer.

## 9. Decisions (yours)

* **D1 binding.** Positional environments (flows' convention, `Config.env`)
  with the printer minting `a0…aN`; not named binders. Recommended: positional.
* **D2 `choose`.** Keep it in `Eff` as the flows-only constructor, refused by
  the native printer, so R3 is an equation rather than a partial map.
  Recommended: keep.
* **D3 `compileRegion`.** Once R3 holds, replace it by `compile ∘ ofFlow` and
  restate S4's lemma once; or keep both. Recommended: replace at the landing.
* **D4 parser order.** §5 (our image, proven) before §6 (recognizer,
  evidence). Recommended: §5 first, §6 as its own lane with foldlab's chassis.
* **D5 placement.** Shared pieces into lean4-typescript (a `Parse` module for
  the canonical reader) and a new small `lean4-lift` for the recognizer
  contract and decoder pattern, versus keeping everything here. Recommended:
  decide after §5 lands and the shapes are real.

## 10. Lanes and order

| lane | delivers | receipts |
| --- | --- | --- |
| A1 AST | `Eff`, `Stmt`, `CauseTerm`, `ActionTerm`, `typeOf`; absorbs `ProgName`/`ActionName` | `DecidableEq`; the constructor↔primitive↔combinator table with rc.112 lines pinned; no `Classical.choice` |
| A2 printer | `print` into lean4-typescript; goldens for every constructor; the fiber rows through `fork-lowering.md`'s spellings | `tsc`/`tsgo` clean at the pin; byte-identical regeneration |
| A3 compile | `compile`, `interpOf`, `eval`; R2 (agreement + progress); `ofFlow`, `ofScript`; R3 | separation-4 gates; the four `#guard` batteries S4 pins, restated |
| A4 parser | `parse` with `parse_print`, `parse_exact` | round-trip goldens |
| A5 recognizer | the lift chassis retargeted; `decodeEff`; taxonomy; corpus trials | two-engine agreement; `decode_exact`; refusal counts per corpus |
| A6 host | R4 over `Eff` (the traces phase) | frame-stream agreement under masks; outcomes |

A1–A3 are one design, landed once (they share the naming and the gates); A4
follows A2 directly; A5 is independent of A3 and can run beside it; A6 is the
traces phase already planned. The witnesses phase (retiring the two old fiber
machines) does not wait on any of this.

## 11. Attacks tried on this design

* *A lambda in user code with arbitrary JS.* Refused (`E-ARG-CLOSURE`); the
  admitted language is first-order by declaration, as foldlab's lift was.
* *`Effect.gen` vs `flatMap` frame shapes.* Handled by §2.1; without it R4 is
  false at the frame level.
* *`Effect.fn`, spans, tracing.* No primitive in `Prim`; refused by name.
* *Nondeterminism.* Effect TS has none in the program; `choose` is a flows
  construct answered by the tape and never printed natively (D2).
* *Handle identity.* First-seen order in the hook, as the tracer already does;
  a program that compares handles by anything else is refused.
* *Fuel.* Carried in `Point` as `Config.fuel` is today; R2 is fuel-exact in
  S4's manner, so a looping program is a stated refusal, not a divergence.
* *A parser in Lean for all of TypeScript.* Not attempted; §5 parses our
  image, §6 uses the admitted engines and crosses as canonical JSON.
