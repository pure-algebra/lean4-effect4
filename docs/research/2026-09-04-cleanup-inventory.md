# Cleanup inventory: the Deep models become the representation

Date: 2026-09-04. Measured on main after `0f5a46d` plus the uncommitted S4/S5/L3
landings (green battery, 282 jobs). Every number below is from the import graph
of the `.lean` sources (`Effect4/`, `Effect4Test/`, `workshop/Deep/`,
`harness/trace/Generate.lean`), not from memory.

## 0. The shape of the tree today

| area | modules | lines |
| --- | ---: | ---: |
| `Effect4/` | 121 | 51,627 |
| `Effect4Test/` | 136 | 36,695 |
| `workshop/Deep/` | 6 | 8,905 |

Of the 121 `Effect4/` modules, the six Deep modules reach **26** (20,484 lines)
and never reach **95** (31,143 lines). "Reach" is the transitive import
closure; a module Deep does not reach is not thereby dead, it is a module whose
justification has to come from somewhere other than the runtime model.

## 1. Buckets

Each row: what it is, the lines it costs (library + batteries), the action, and
what has to be true before the action is safe.

### A. Deep's foundation. Keep, and promote Deep onto it.

| module(s) | lines | why it stays |
| --- | ---: | --- |
| `Runtime.Runtime` | 3,370 | rc.112 frame machine (`Prim`, `FrameFiber`, `PrimInterp`, structural `popFrom`) — the core Deep steps |
| `Runtime.Scope`, `Runtime.ScopeMachine` | 1,765 | the rc.112 `Scope` model Deep.Stores/Layer use directly (`make`/`fork`/`close`/`addUnsafe`…); `ScopeMachine` is used by `RegionSimulation` |
| `Semantics.Cause`, `Semantics.Exit` | 1,293 | the error channel everywhere |
| `Semantics.FrameSimulation`, `Semantics.RegionSimulation` | 3,618 | the flow→frames compile (`compileRegion`) that `Deep.ForkFlow` delegates to, with S4's agreement lemmas |
| `Flow.Region/Decision/Interrupt`, `Semantics.Denotation/Runs/Fuel/Frontier/Observation` | 2,773 | the flow language and its runner — see decision E′ below |
| `Context.Key`, `Data.Row` | 789 | `ServiceKey` identity, requirement rows |
| `Meta.Derive`, `Target.EffectV4`, `Target.ScriptFlow`, `Target.Simulation` | 1,522 | the family DSL, the service-row/script carrier, the frame→trace projection |
| `Concurrency.Fiber`, `Concurrency.Interrupt` | 117 | fiber ids, interrupt requests |

### B. Shrink to vocabulary: the two old fiber machines

`Concurrency.Scheduler` (2,761) and `Concurrency.Supervision` (1,681) are in
Deep's closure only because `Deep.Fibers` keeps three *projections* onto them
(`toCore` → `FiberState`, `toSup` → `Supervision.Fiber`, `toSched` →
`Effect4.Machine`, `Fibers.lean:210/226/499`) and reuses their vocabulary.
What Deep actually names from them:

* from `Supervision`: `ForkOptions`, `MaskMode`, `ObserverMode`, `ScopeMode`,
  `RaceAllState`, `raceComplete`, `interruptCause`, `Subscription`, and the
  `Fiber` record for the projection only;
* from `Scheduler`: `MaxOpsBeforeYield`, `PreventSchedulerYield` (reference
  keys), and `Machine` for the projection only.

Action: move the vocabulary (≈ 300 lines) into a small module beside
`Concurrency.Fiber`; delete the three projections from `Deep.Fibers`; delete the
two machines (≈ 4,100 lines: 224 theorems, 71 defs) with their batteries
(`FiberRepresentativeContract`, `FiberSupervisionContract`, both axiom reports,
`FiberAssurance` 2,512 lines, the two `Counterexamples.Concurrency.Fiber*`
files — 6,499 test lines together with the race bucket in C).

What must be true first: **the census witnesses.** `Effect4Test/Audit/
RuntimeCoverage.lean` (4,007 lines, 154 dispositions) joins the rc.112
mechanism census to Lean witnesses, and today 630 of its references are
`Effect4.Supervision.*` theorems and 818 are frame-machine theorems that stay.
The witnesses phase you already ruled next is exactly re-pointing those 630 at
Deep theorems (`Deep.Witnesses` is the seed). Until that is done the two
machines cannot go without the census gate going red. `generated/
fiber-assurance.tsv` (232 KB) is regenerated from the new witnesses at the same
time.

### C. Delete: superseded outright by Deep

| what | lines (lib + tests) | superseded by | also goes |
| --- | ---: | --- | --- |
| `Concurrency.FiberFamily` (M3 sequential projection) | 502 + 421 | `Deep.Fibers` + the L1 fiber profile in `Deep.ForkFlow` | `harness/trace/fiber-tail.ts`, `fiber-fixture.ts`, `generated/traces/fiber/`, Generate's `fiber-*` arms, register rows E4-SEM-CE-010/011, `docs/FIBER-DAG.md`. Keep L2's `fibers-tail.ts`/`fibers-fixture.stub.ts` (the new profile). Its "depth two" refusal is also stale: `Meta.Derive` admits depth three and `DeferredFamily.poll` already spells `Option (Except Nat Nat)`. |
| `Concurrency.Race` (binary race representative) | 681 + 841 | `Deep.Fibers.Race` over `RaceAllState` | `RaceRepresentativeContract` (red by design since its birth), `race-representative.contract.md`, `docs/RACE-DAG.md` |
| `Runtime.LiveStack` | 459 + 397 | frame facts about `Runtime.lean`; nothing cites them (0 census references) | `live-stack-assurance.json` (445 KB), `LIVE-STACK-DAG.md`, `LIVE-STACK-IMPLEMENTATION.md`, `live-stack.contract.md`, `scope-restoration.mjs`? (check) — **or fold** the two theorems worth keeping into `FramesContract` |
| `Runtime.ScopeRestoration` | 180 + 377 | same category: mask restoration through `popFrom`, a frame fact | `scope-restoration.contract.md` — fold the statement into `ScopeMachineContract` or delete |
| the 45 eight-line "Owner:" stubs (`Audit.*`, `Channel.*`, `Classification.*`, `Layer.Build/Description/Laws/Memo/Provision`, `Meta.Emit/Introspection/Registry`, `Runtime.Lifecycle/ManagedRuntime/Resource`, `Schedule.*`, `Semantics.Configuration/Step`, `Stateful.Deferred/PubSub/Queue/Ref/SubscriptionRef`, `Target.TypeScript.Decode/Type`, `Transaction.*`, `Data.Canonical/Identifier`, `Foreign.*`, `Context.Environment/Service/Requirement`) | 363 | nothing; they were the old roadmap's placeholders | their 45 import lines in `Effect4.lean`, `docs/CLASSIFICATION-DAG.md` |
| `Protocol.*` (4 modules) | 239 + 582 | an abandoned lane; its battery `ByteParserContract` names types that never existed | the `Effect4TestProtocol` lib in `lakefile.toml` |

C is safe now, except that FiberFamily's goldens are inputs to
`scripts/check-trace-host.sh`; the script's `fiber` family section goes with it.

### D. Decide: the old flow semantics (5,073 + 1,206 lines)

`Semantics.Approximation` (2,250), `RegionDenotation` (1,051), `RegionTotal`,
`RegionSafety`, `Logic`, `PlanInversion`, `Equivalence`, with twelve batteries
and three contracts (`flow-denotation`, `region-safety`,
`region-total-denotation`). This is the denotational semantics of flows built
*before* the frame machine existed. With Deep as the representation, a flow's
meaning is its compile to frames plus the machine (S4's agreement lemma is what
ties the runner to it). Recommendation: **retire**, in two steps — everything
but `PlanInversion` now; `PlanInversion` (388) once
`Target.TypeScript.SkeletonSemantics` (which uses it for the structured-form
proof) is restated over frames or dropped with the structured form (G).

### D′. Decide: the Flow runner itself

`Flow.Region`'s `regionLoop`/`runRegions` is a third executable beside the
Effects surface and the frame machine. It is what the simulation proves the
compile agrees with, and what generates the flow goldens today. Two honest
options: (i) keep it as the reference interpreter and golden generator (cheap,
2,773 lines already in Deep's closure); (ii) make `Deep.drive` the only runner
and regenerate goldens from it, then drop the runner and the simulation's
runner-side lemmas. (i) costs nothing now; (ii) is the purer end state and
belongs to the traces phase. Recommend (i) until the traces phase, then decide.

### E. Rebase, do not delete: the L3 store families (3,340 + 2,916 lines)

`RefFamily`, `DeferredFamily`, `ScopeFamily`, `ContextFamily`, `LayerFamily`
are the *lowering rows* for the stores (the `effect_signature` tables, the
wire, the goldens). Their Lean handlers each keep a private store
(`ContextStore`, `DeferredStore`, …) that duplicates `Deep.Stores`,
`Deep.Context`, `Deep.Layer`. Action: keep the rows and batteries; replace each
handler's store with a projection of the Deep store (one source of truth);
merge the five `-- SHIM:` duplicates in `Deep.Layer` into `Deep.Stores` at the
same time (S5 §6). `Deep.Layer` already imports `LayerFamily` for the forgetful
join, so the direction is settled.

### F. Keep: the lowering (9,700 + 4,462 lines)

`Target.TypeScript.*` minus the schema pair: skeleton and renderer, the
dispatch/region/structured forms, the script denotation, the trace wire, L1's
fiber profile. This is the lowering the goal requires. The one optional cut is
the structured form (`StructureDominators/Laws/Order/Semantics`,
`SkeletonSemantics`, `StructuredLower`: ≈ 6,400 lines) if dispatch-only output
is ever acceptable; no reason to take it now.

### G. Out of scope of this refactor: Schema (11,401 + 4,895 lines)

`Schema.*`, `Data.Json/Optic`, `Target.TypeScript.Schema/EffectfulField`, the
30 schema batteries, `schema-structural-assurance.tsv` (258 KB), and five
`SCHEMA-*` docs (200 KB). Nothing here is superseded by Deep; it is the other
half of the Effect v4 reification. Keep unless Schema leaves the project's
scope, which is a separate decision.

### H. Promote Deep — **done 2026-09-04**

Landed as `Effect4/Deep/*.lean` (module names `Effect4.Deep.X`), imported from
`Effect4.lean`, the `Deep` lean_lib removed; the gate audits the six modules
(265 modules, 25,292 declarations, green) after one proof repair
(`refMake_twice_distinct`, `simp` had reached `Classical.choice`). The three
projections are kept for this landing as planned. The original text follows.

Move `workshop/Deep/*` under `Effect4/` (either `Effect4/Deep/` or straight
into `Runtime/Fibers.lean`, `Runtime/Stores.lean`, `Context/Environment.lean`,
`Layer/Store.lean`, `Flow/Fork.lean`, replacing the stubs of the same names),
import them from `Effect4.lean` (the module-closure gate requires it), drop the
`Deep` lean_lib. `Deep.Witnesses` becomes the witness module the census joins
to. This is the first step, before B, because B's witnesses cite Deep names.

### Landed 2026-09-04 (cut 1), by the ruling "keep what is proven, drop the testing garbage and what Deep directly replaces, plus workshop and worktrees"

Removed, gate green afterwards (209 modules, 24,734 declarations, 235 jobs):
the 45 stubs; `Protocol.*` with its red battery and lib; `Concurrency.Race`
with its red contract, packet, DAG and script; M3 `Concurrency.FiberFamily`
with its three batteries, tail, fixture, goldens, generator arms, host-check
section and two register rows; `docs/CLASSIFICATION-DAG.md`; `workshop/`; the
stale S1 worktree. `known-red.txt` is empty. Kept by the same ruling, being
proven: `Runtime.LiveStack`, `Runtime.ScopeRestoration`, bucket D's old flow
semantics (still undecided, still green), and everything the witnesses phase
gates (bucket B).

## 2. Records that go with each bucket

| record | today | after |
| --- | --- | --- |
| `test/counterexamples/REGISTER.md` | 197 rows | drop the rows of C/D; keep the rest |
| `test/contracts/*.contract.md` | 43 | drop `fiber-representative`, `fiber-supervision`, `race-representative`, `live-stack`, `scope-restoration`, `flow-denotation`, `region-safety`, `region-total-denotation`, `algebra-*`, `foldlab-vendor` (algebra now lives in lean4-effects) |
| `docs/*.md` | 27 files | drop `FIBER-DAG`, `RACE-DAG`, `SUPERVISION-DAG`, `SUPERVISION-IMPLEMENTATION`, `LIVE-STACK-*`, `CLASSIFICATION-DAG`, `ALGEBRA-PACKAGE-PLAN`, `EFFECTS-SPLIT-PLAN` (done); rewrite `FRAMES-DAG`, `TRACE-DAG`, `SCOPE-DAG`, `RUNTIME-COVERAGE`, `ARCHITECTURE` around Deep |
| root | `COORDINATION.md` 175 KB, `PLAN.md` 20 KB, `misty-frolicking-naur.md` 27 KB (a v3 plan for trace-driven lowering), `PORT-MANIFEST.md` 93 KB | archive the first three under `docs/history/`; keep `PORT-MANIFEST.md` (it is the provenance record) |
| `generated/` | census TSVs, `fiber-assurance.tsv`, `live-stack-assurance.json`, traces per family | regenerate `fiber-assurance` from Deep; delete `live-stack-assurance.json` with C; regenerate traces in the traces phase |
| `harness/trace/` | 41 files | drop `fiber-tail.ts`/`fiber-fixture.ts` (M3); replace the six `*-fixture.stub.ts` with generated fixtures; rewrite `context-tail.ts` against the generated rows |

## 3. Order

1. **H** promote Deep (one commit; keep the three projections for this commit
   so nothing else moves).
2. **Witnesses phase**: Deep theorems for the 630 census rows now witnessed by
   `Supervision`; regenerate `fiber-assurance.tsv`; `RuntimeCoverage` re-points.
3. **B + C + stubs** in one commit each, batteries with them, the gate green at
   each step.
4. **D** (retire the old flow semantics, `PlanInversion` last), **E** (rebase
   the store handlers), then the traces phase decides **D′**.
5. **G** untouched.

Net effect if D, D′(ii) and the fold in C are all taken: `Effect4/` goes from
51.6k to roughly 32k lines, `Effect4Test/` from 36.7k to roughly 22k, and there
is one fiber model, one scope model, one store model, one context model.

## 4. The `effects` dependency, assessed

lean4-effects v0.8.0 (`a4ee7a1`) supplies three things here, and nothing in the
runtime model: the **flow language** (`Effects.Flow.Block/Region/Checked`,
`RawFlow`, `admit`/`admitRegions`, `RegionClause`) — the program syntax the
lowering emits and `compileRegion` consumes; the **trace alphabet**
(`Effects.Trace.Val/Event/Mask/ToVal/project`, `Outcome` with `defect` and
`interrupted`) — the wire; and the **family algebra** (`Family`, `Signature`,
`Program`, `interpret`, `traced`/`tracedExcept`) — the carrier of the
`effect_signature` DSL. Two modules use `Effects.Algebra.Sum/Laws`.

No defect in the library was found in this work. The v0.8.0 boundary release
(`errorTy : Op → Option Ty`, published reachability lemmas) was adopted cleanly
and let us delete the lemmas we had been duplicating locally. The flaws we
found were all in *our* models — the fused `popFrom` against rc.112's
`AsyncFinalizer`, `finalizerOr` reading the stack head instead of the delivery
frame, the region continuation resuming at the enter's configuration, nested
commands after `exitFiber`, Layer guards pinned to wrong behaviour,
reference-blind `getOption`, `merge`'s empty-side identity, `LayerId` as
identity — and every one is fixed above.

Two things about the *arrangement* are worth saying plainly. The tree has two
program representations by design — Effects flows/programs on the surface,
rc.112 `Prim` frames in Deep — bridged by the compile and S4's agreement lemma;
that is the intended architecture, not a flaw, and it is why the flow runner
(D′) is now optional. And the wire's per-answer spelling still cannot carry a
full `Exit` (a `Cause` with interrupt or defect arms) even though the `done` row
can say `interrupted`/`defect`; that limit is in `Meta.Derive`'s spelling
stratum and the answer profile, not in `Effects.Trace`, and it is the
traces-phase item already recorded in `DeferredFamily` and `FiberFamily`.

## 5. The DSL: keep the portable layer, retire the service wall around the environment's own primitives

> **Superseded ruling (2026-09-04).** The first draft of this section
> recommended retiring the DSL outright and printing Effect TS from an
> Effect-specific AST. That was wrong about what `Effects` is for: it is the
> *portable* effect layer — a program written against an `Effects` family or
> flow is the artefact that runs in the Lean model, in Effect TS, in the WHATWG
> reification, and in whatever supplies handlers and a lowering next. The
> corrected ruling is §5′ below; the draft is kept underneath it because its
> facts (public spellings, the run-loop hook, the tape scheduler) are what §5′
> rests on.

### 5″. Ruling (user, 2026-09-04): two routes, one model

Keep the DSL **as the fine-grained formalisation of the Effect TS surface**:
every rc.112 operation stays a declared row with its spelling, its line
citation and its Lean semantics. Add the **native route** beside it: lowering
with Effect primitives, and Deep as the machine, wherever fidelity needs it.
Nothing that gives native capability or fidelity today is to be lost, and the
Deep model must remain usable as the semantics of either route.

What that fixes in §5′ below:

* The native families' rows **and handlers** stay. The handlers are the
  API-level spec of each operation; Deep is the mechanism-level truth. The two
  are tied by *forgetful joins* — theorems that the family handler is a
  projection of the Deep store or machine, in the shape `Deep.Layer` already
  has for `LayerFamily` (`forget_parent`, `forget_fresh`, …). Bucket **E** is
  therefore "prove the joins for `Refs`, `Deferreds`, `Scopes`, `Contexts` and
  the fiber profile", not "delete the handlers". One truth, two views.
* The service lowering stays for every family, and the **native lowering
  mode** is added as a per-family or per-row option, so a program can be
  emitted either as service calls (traceable at the request/answer wall) or as
  direct rc.112 calls (compared at the frame level through the run-loop hook
  and the tape). Both faces are generated from the same rows.
* The service-level goldens stay as evidence for the service route; the
  native route adds frame-level receipts rather than replacing them.
* Retired from §5′'s list: nothing beyond what §1's buckets B, C, D and the
  stubs already retire. The tails and fixtures stay for the service route;
  the six `*-fixture.stub.ts` are still replaced by generated fixtures.

The net of §1 is unchanged by this ruling except bucket E: promote Deep,
witnesses, shrink the old machines, delete the superseded modules and stubs,
retire the old flow denotational semantics, prove the joins, add the native
mode.

### 5′. The corrected split (as amended by 5″)

| layer | what it is | keep / retire |
| --- | --- | --- |
| `Effects` (algebra, `Family`, `Program`, `interpret`, `Flow`, `Trace`) | the portable program language and its trace alphabet | **keep** — this is the unified effects implementation, and lean4-effect4 is one reification of it |
| `effect_signature` / `effect_program` / `effect_atoms` (`Meta/Derive.lean`) | the front-end that declares a `Family` once for every face | **keep** — it is how a portable interface is written; the one change is a second lowering mode below |
| flow lowering (`FlowLower`, `RegionLower`, `StructuredLower`, `Skeleton*`, `Structure*`) | the Effect TS spelling of the portable *control* structure (blocks, branches, regions) | **keep** — this is the environment adapter for control |
| `compileRegion` / `compileFork`, `FrameSimulation`, `RegionSimulation` | running an `Effects` program *in the Lean model* of Effect TS (flows → rc.112 frames), with the agreement lemma | **keep** — this is what "run it in the Effect TS environment, in Lean" means |
| service-wrapper face of the **native** families (`Refs`, `Deferreds`, `Scopes`, `Layers`, `Contexts`, the fiber profile): the `Context.Service` classes, `*-tail.ts`, `*-fixture*.ts`, the private Lean handlers (`ContextStore`, `DeferredStore`, …), their service-level goldens | a service wall around operations the environment *natively has* | **retire** — replaced by native-call printing, Deep as the semantics, and frame-level evidence |
| user families (the job queue and whatever comes next) | services the environment does *not* natively have | **keep the service lowering** — the environment cannot know their semantics; the Lean handler is the spec and the request/answer trace is the right observation point |

The distinction the first draft missed: a family is portable when its
operations are *the program's* effects, and a wrapper when its operations are
*the environment's* primitives. `Refs.getAndUpdate`, `Layers.buildWithMemoMap`
and `fork` are Effect TS's own API. Wrapping them in a `Context.Service` so
that a trace exists gave the DSL a service wall to observe, but it also made
the host run the tail's wrapper frames rather than the program's, and it forced
every runtime object into a wire handle. Those rows do not need a service:
they need a lowering that prints the real call, a model that is Deep, and
evidence taken at the frame level.

**The one change to the DSL.** A family declared `native` (or a per-row
attribute) lowers its performs as direct rc.112 calls — `yield* Ref.get(r)`,
`Effect.forkChild(root)`, `Scope.addFinalizer(scope, fin)`, `Layer.effect(…)` —
instead of `yield* service.op(…)`, and takes its Lean semantics from the Deep
stores and machine instead of a private handler. The rows keep their
declaration, their TypeScript spellings and their rc.112 line citations (that
is the API table the printer needs); `encodeParam`/`encodeAnswer` stay for
the rows a trace still names. User families are unchanged.

**Evidence for native rows** moves to where the model lives: outcome equality
through `runSyncExit`/`runPromiseExit` at the same decision tape (the
`TapeScheduler` already drives rc.112's yields from the Lean tape), and frame
agreement through the run loop's own per-primitive hook
(`currentTracerContext(current, fiber)`, `internal/effect.ts:653-655`, the
public `Tracer.context`) plus the patched copy's observation hunks
(`frame.pop`, `scope.close-*`, `layer.memo-build`), which today are recorded
and never compared. Deep's `RunEvent`/`FrameEvent` stream is the Lean side.
Object identity on the host is first-seen order in the hook, as the tracer's
`registerHandle` already does; rc.112 internals with no public API (the
children set, the raw layer builder) become unreachable from a printed
program rather than reachable through a cast, which is the honest position.

**Portability caveat to carry forward.** Regions (`enter`/`acquire`/`leave`)
are portable resource scoping already. Forks are currently an Effect-flavoured
alphabet (the fiber profile rows). A second environment without fibers will
need fork to be a flow-level construct with environment-specific semantics, or
to be refused there; that is a question for `Effects`, not for this cleanup.

**What this changes in §1.** Bucket **E** (rebase the family handlers on Deep)
becomes "delete the private handlers and tails, keep the rows, lower natively";
bucket **F** stays; **D′** resolves to keeping the flow runner as the reference
interpreter, since the flow language is the portable syntax; the `effects`
dependency stays. The net retirement is smaller than the first draft claimed:
the native families' handlers, tails, fixtures, tracer proxy and service-level
goldens (≈ 3,300 Lean lines, ≈ 20 harness files, ≈ 50 goldens), not the DSL,
not the flow language, not the lowering.

**Recommendation.** Keep `Effects` and the DSL. As the traces phase: add the
native lowering mode, retarget the native families' semantics to Deep, build
the hook-based harness, then delete the service wall around them in one commit.

### 5 (first draft, superseded — facts retained)

The question: keep `effect_signature`/`effect_program`/`effect_atoms`
(`Meta/Derive.lean`) and the service-shaped lowering they feed, or write
programs that *are* Effect TS programs and print those.

**What the DSL is.** A program is written against a *service* (`Contexts`,
`Layers`, `Refs`…): every operation is a request/answer pair, the Lean face
interprets it with a Lean handler, the TS face runs it against a `Context.Service`
whose implementation (`harness/trace/*-tail.ts`) calls rc.112, and the two
traces are compared under masks. The service wall is the observation point, and
the wire (`Effects.Trace.Val`) is why every object is a handle. Everything from
`Effect4/Meta/Derive.lean` through `Target/TypeScript/*` (minus the schema
pair), the five families' handlers, the fixtures, tails, tracer proxy and
goldens exists to serve that arrangement: ≈ 13k Lean lines and 25 harness
files.

**Why it is now unnecessary.** Deep is a program-carrying frame machine over
rc.112's own primitives, and the 17 `Prim` constructors each have a public
spelling in the pinned install (`Effect.sync/suspend/succeed/fail/failCause/
withFiber/callback/onExit/catchCause/matchCause/flatMap/yieldNowWith/
uninterructible/interruptible/whileLoop/exit`; `iterator`, `exitFrame`,
`asyncFinalizer`, `setInterruptible` and `yieldableError` arise only through
`gen`, `exit`, `callback`, the mask combinators and `fail`, which is exactly
how a printer would emit them). So a Lean program at the machine's level *is*
an Effect TS program modulo printing, and the evidence channel can move from
service-level request/answer rows to the level the model actually lives at:

* **outcome**: `Effect.runSyncExit`/`runPromiseExit` of the printed program
  against the machine's `Exit`, at the same decision tape (the harness's
  `TapeScheduler` already drives rc.112's yield decisions from the Lean tape);
* **frames**: rc.112's run loop calls `currentTracerContext(current, fiber)`
  before every primitive it evaluates (`internal/effect.ts:653-655`, the public
  `Tracer.context` hook), and the patched copy already records `frame.pop`,
  `frame.deferred-interrupt`, `scope.close-*` and `layer.memo-build`
  (`harness/trace/patched/patch-manifest.json`); Deep's `RunEvent`/`FrameEvent`
  stream is the Lean side of that comparison. Today those rows are "recorded,
  never compared" (`trace-patched-host.contract.md`); this makes them the
  comparison.

The service wall hid the structure that matters: behind `yield* refs.get(r)`
the host's frames are the tail's `Effect.sync` wrappers, not the program's.
Printing the real program means the host runs the real frames.

**What a first-order syntax still has to exist.** TS can be printed only from
syntax, never from a Lean closure, so *some* first-order program AST stays: a
small `Eff` inductive whose constructors are the Effect TS combinators over a
tiny pure-expression language (naturals, booleans, pairs, lists, options,
results, named host atoms) — i.e. the AST of the Effect TS subset we emit. Its
printer is structural; its compile to `Prim` is the defunctionalisation that
names each continuation and builds the `PrimInterp` table; its semantics is
the Deep machine. That replaces `Effects.Flow` (blocks/regions/admission),
`compileRegion`/`compileFork`, and the flow runner in one move: the flow
language was the DSL era's first-order syntax, and the region/fork compiles
were the bridge from it to frames. `PureTerm` and the atom concept survive as
the expression language; the macros do not.

**What retiring changes in §1.** Bucket **E** (rebase the family handlers on
Deep) is cancelled — the families go with the DSL, rows and goldens included,
after the new channel covers the same rc.112 facts (the L2/L3 rows' line
citations move into the printer's API table as data). Bucket **F** (lowering,
9,700 + 4,462 lines) is retired except what the new printer reuses
(`TypeScript` rendering primitives from lean4-typescript, the reserved-name
and namespace logic). **D′** is decided: the flow runner goes with the flow
language. `Semantics.FrameSimulation`/`RegionSimulation` (3,618) and
`Deep.ForkFlow` (1,754) go once the new AST's compile to `Prim` is in and the
S4 agreement lemma is restated for it (the lemma's *shape* — the walk is the
runner — carries over; the statement changes). The `effects` dependency
reduces to `Effects.Trace` or to nothing (Deep's event alphabet and
`Outcome` replace it); lean4-effects stays a library for other projects.

**What it costs.** A new lane about the size of S4 plus L1: the `Eff` AST and
pure expressions (~600 lines), the printer (~800), the defunctionalising
compile with its agreement receipt (~1,500), the hook-based harness (one
tail, one tracer, ~500 TS lines), and re-establishing the store facts as
direct programs (the 34 goldens become roughly as many direct programs). What
it retires is ≈ 20k Lean lines and most of `harness/trace/`. Two things
genuinely get harder: object identity on the host is by first-seen order in
the hook rather than by a wire index (the tracer's `registerHandle` already
does this); and rc.112 internals with no public API (the children set, the raw
layer builder) are unreachable from a printed program rather than reachable
through a cast — which is the honest position.

**Recommendation.** Retire. Do it *as* the traces phase rather than after it:
build the `Eff` AST, printer and hook harness first, prove the compile's
agreement, then delete the DSL, the families, the flow language and the
service lowering in one commit with the gate green. Do not spend the
witnesses phase on bucket E or on regenerating family goldens.
