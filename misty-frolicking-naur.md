# Plan: trace-driven lowering into Effect v4 with an instrumented rc.112

Status: v3 (research and both planning reviews folded in). Decisions still open are
listed at the end.

## Context

The chain works end to end (Lean family → generated Effect v4 module → `tsc.original`,
effect-tsgo strict, node run equal to the Lean receipt), but nothing establishes
*behaviour* beyond one host run, and every proof bridge (Flow ↔ frame machine, Scope,
scheduler) is pending. Ruling: working code with high rigor, fast. Proofs only where they
are one induction; everything else by executable evidence with the gaps recorded as data;
all internals viewable.

The method: one shared **service-level trace alphabet**; every face emits it (the
algebra through a tracing service, the Flow runner, the host through a Tracer hook and a
service proxy); rigor is **trace agreement under a named mask**, checked on golden
programs and on generated ones; a **self-checking coverage ledger** per lowering rule
(golden, host, property, type receipt, proof). No simulation theorem in this phase; the
frame-level stream is recorded, never compared, until a Prim model exists.

Inputs (verified this session): the standup (Effects v0.2.0 `fa3cdc9`, typescript v0.1.1
`8f17b88`, Effect4 `6c9f479`), the rc.112 host survey, the codex shared-semantics report,
the js_of_ocaml algorithm extraction, and the repo convention survey. Key host facts:
`Tracer.context` runs on every runtime step (`dist/internal/effect.js:462`) and returns
what `evaluate` returns, so a trace host needs no patch; primitives carry
`~effect/Effect/identifier`; `Effect.runFork(p, { scheduler })` takes a `MixedScheduler`
subclass; the dist is plain ESM, patchable in a copy; a source build is infeasible.
effect-tsgo has no types API. JS `finally` in a generator does not run on a yielded
failure. Scope closes state first, LIFO, idempotent.

## Rulings (edit here, not in packets)

- **R1 Alphabet home and level.** Service-level only, minted in lean4-effects
  `Effects/Trace.lean` (parametric, host-free); Effect4 consumes it in
  `Effect4/Semantics/Observation.lean` (masks, agreement), which imports neither Runtime
  nor Concurrency. Projections from `FrameEvent` and the scheduler `Event` are P-T11
  material in `Effect4/Target/TypeScript/Simulation.lean`, the module allowed to see
  both (FRAMES-DAG separation 7 stays intact).
- **R2 Tracing is an around-wrapper, not a homomorphism.** `Family.Service.traced`
  logs per operation; its law is `interpret_traced_fst` (forget the log, recover the plain
  interpretation), one induction. `mapHom` of a lift logs nothing.
- **R3 Host instrumentation is layered.** Phase 1 zero-patch (Tracer.context, scheduler
  subclass, metrics service, withFiber). Phase 2 a patched copy under
  `harness/trace/patched/` with its own pin and patch manifest, never under `vendor/`.
- **R4 Cleanup never lowers to `try/finally`.** Regions lower to `Effect.onExit` /
  `Effect.acquireRelease` inside `Effect.scoped` only.
- **R5 Two error readings, two row shapes.** Data: answer `Except E A` spelled
  `Either.Either<A, E>`. Abort: `OpRow.error` set, service kind `X.Service (ExceptT E M)`,
  method `Effect.Effect<A, E>`. An `Except` answer is never rendered as `Effect<A, E>`.
- **R6 Decisions are a request/answer protocol.** A `Decisions` family; the *choice
  tape* is `List (DecisionId × Bool)` consumed by occurrence with a site check (mismatch =
  refusal, exhaustion = live frontier). The scheduler's tape is a different object
  (`scheduleTape`), fixed to the single-fiber preset in this phase.
- **R7 Dispatch form first.** Flow lowers to `while (true) { switch (block) … }` for every
  admitted graph; the structured form is an optimization behind a reducibility check,
  re-derived from js_of_ocaml; both must agree on every trace (a pure-Lean theorem).
- **R8 Evidence moves a rule, proof is recorded.** States `absent | pinned | checked |
  covered | proved-lean-side`; no percentage; host evidence never fills `proof`, a Lean
  theorem never fills `host`, and nothing here touches `generated/effect-runtime-census.tsv`.
- **R9 Flow v2 before Flow lowering.** Today's Flow (one payload replaced by each
  answer, no atoms) cannot express `let x ← get; put (succ x); return x`. Lowering from
  Flow waits for block parameters and region rows (Effects v0.4.0, one bump). The
  Program-face pipeline (Script → traces) ships first.

## The shared alphabet (frozen in P-T1)

```lean
namespace Effects
inductive Trace.Val | unit | nat (n : Nat) | int (i : Int) | bool (b : Bool) | str (s : String)
  | pair (l r : Val) | none | some (v : Val)              -- List = right-nested pairs; Except = pair (bool ok) payload
class Trace.ToVal (α) where toVal : α → Trace.Val        -- Unit Nat Int Bool String Prod Option List Except
inductive Trace.Outcome (υ) | success (v : υ) | failure (e : υ) | interrupted
inductive Trace.Event (ω υ δ ρ : Type u)
  | op (name : ω) (request : υ) | answer (name : ω) (value : υ) | failed (name : ω) (error : υ)
  | decide (site : δ) (branch : Bool)
  | enter (region : ρ) | leave (region : ρ) (outcome : Outcome υ) | finalizer (region : ρ) (outcome : Outcome υ)
  | done (outcome : Outcome υ) | frontier
structure Trace.Mask where ops answers decisions regions finalizers outcome frontier : Bool
def Trace.project (m : Mask) : List (Event …) → List (Event …)   -- filter; masks are projections
def Mask.outcomeOnly / m1 (+ops +answers +failed) / m2 (+decisions +regions +finalizers) / full
theorem project_project, project_full, m1_refines_m2 (project m1 = project m1 ∘ project m2)
def Family.Service.traced (nameOf) (encodeParam) (encodeAnswer) (service : F.Service M)
  : F.Service (StateT (List (Event ω υ δ ρ)) M)
theorem Family.Service.interpret_traced_fst [LawfulMonad M] :
  (·.1) <$> (interpret (service.traced …).toHandler p).run log = interpret service.toHandler p
```

Wire form (TSV rows, JSON scalars in cells): `op\tget\t[]`, `answer\tget\t41`,
`decide\t3\ttrue`, `enter\t1`, `finalizer\t1\t{"failure":"boom"}`, `done\t{"success":42}`,
`frontier`. Outcome under M1 is `(tag, reason tags in order, fail payload)`: annotation-blind
and host-error-identity-blind by decision (FRAME-FB-STACK-ANNOTATION, FRAME-FB-HOST-ERROR).
The error carrier order is `ExceptT ε (StateT log M)` so the log survives failure.

## Packets

Each: fence, declarations, lemmas (one induction or none), gates, acceptance, rows to seed.
Register ids: take the next free id at claim time (`E4-SEM-CE-`, `E4-TARGET-CE-`,
`E4-FLOW-CE-`; a new `EF-<AREA>-CE-` family in lean4-effects for rows whose witness lives there).

### P-T0 Prerequisites (blocks everything; ~1 day)

1. Axiom gate: `Effect4Test/Audit/AxiomGate.lean` `targetImplementationModules := [`Effect4.Meta.Derive]`
   (16 of its 42 declarations reach `Classical.choice`; the gate has not run on this tree,
   `./scripts/test-trust-gate.sh` is red at HEAD). Acceptance: trust gate green with
   known-red unchanged.
2. Pins: push lean4-effects `fa3cdc9` and lean4-typescript `8f17b88` (repo creation under
   pure-algebra), `lake update effects typescript` in Effect4 and whatwg, commit manifests,
   remove the path overrides from the workflow. Acceptance: `lake build Effect4` without the
   manifest warning; `harness/effect-v4-family/check.sh` green. (Open decision D3.)
3. Move `harness/effect-v4-family/probe-trace.ts` to `harness/trace/tracer.ts` (P-T3 seed).
4. `COORDINATION.md` claim rows for every fence below (re-read first; `generated/**`,
   `vendor/**`, `REGISTER.md` rows are currently claimed by Codex).
5. `docs/TRACE-DAG.md`: graph `TRACE-PG-AGREEMENT`; `semantics` and `bridges`
   `required-open` ("no simulation theorem in this phase"); `docs/LOWERING-COVERAGE.md`
   owns the ledger vocabulary; both added to the AGENTS.md authority map.

### P-T1 Trace alphabet and traced service (lean4-effects v0.3.0; ~250 Lean + battery)

Fence: `Effects/Trace.lean`, `Effects.lean`, `EffectsTest/Trace/{TraceContract,AxiomReport}.lean`,
`EffectsTest/Counterexamples/Trace/*.lean`, `test/contracts/trace.contract.md`,
`docs/CLAIM-BOUNDARY.md` (v0.3.0 entry), `lakefile.toml` version. Declarations as above.
No `String` traversal in this module (axiom ceiling); rendering lives in Effect4.

Rows: `EF-TRACE-CE-001` "a tracing handler is `mapHom` of a lift" (logs nothing; repair:
around-wrapper + `interpret_traced_fst`); `-002` "answers are redundant" (equal op-only
traces, different answers; repair: M1 keeps `answer`); `-003` "agreement without a mask"
(repair: agreement is always per named mask, `m1_refines_m2` tested by a pair that agrees
under M1 and differs under M2).

Acceptance: `lake build` (gate), trust self-test, `#print axioms` of the two lemmas within
the ceiling; then tag and bump.

### P-T1b Effect4 consumer (~150 lines)

- `Effect4/Semantics/Observation.lean` (stub today): `abbrev Trace.Event := Effects.Trace.Event String Trace.Val Nat Nat`,
  `maskTable : List (String × Mask)`, `agree (mask) (l r) : Bool`, `agree_refl`. No
  Runtime/Concurrency import.
- `Effect4/Meta/Derive.lean`: `effect_signature X` also emits `X.Name.spelling`, per-op
  `ToVal` encoders by match arm (so instances resolve at the `abbrev` types), and
  `X.traced : X.Service M → X.Service (StateT (List Trace.Event) M)`. `OpRow` gains
  `pure : Bool := false` and `error : Option (String × String) := none` (defaults keep
  `fixture.ts` bytes).
- `Effect4/Target/TypeScript/EffectV4.lean`: `ServiceRow.rowsDecl` emits
  `export const CellRows = { get: { params: 0 }, put: { params: 1 } } as const` so the host
  proxy knows arities; `Script.lower` is split into one `def` per rule with docstring tags
  `lowering: rule.<name>` (`service-acquire`, `perform-bind`, `perform-discard`,
  `nullary-value`, `atom-call`, `ret`).
- Battery `Effect4Test/Semantics/ObservationContract.lean`; row `E4-SEM-CE-` "host mask
  table drifts from Lean's" (repair: `generated/traces/masks.tsv` is generated from
  `maskTable`). Rendering to TSV/JSON lives in `Effect4/Target/TypeScript/Trace.lean`,
  an exact-module exemption.

### P-T3 Host tracer (effect4-tools + `harness/trace/`; ~400 lines TS)

`packages/harness/trace.mjs` (`effect4-trace <dir> --goldens <dir> --masks masks.tsv
[--batch]`) and `harness/trace/{tracer.ts, Generate.lean, fixture.ts, atoms.ts, trace.tail.ts,
tsconfig.json, check.sh, host-pin.json}`.

`tracer.ts`: `traceService(rows, impl, sink)` (op/answer/failed around every method; nullary
ops are Effect values); `decisionsFromTape(tape)` (site mismatch → defect `TAPE_SITE_MISMATCH`,
exhaustion → sentinel exit mapped to `frontier`); `withBudget(n)` as the `Tracer.context`
hook (counts primitives, records `frames.jsonl` = second, non-evidence stream of op names and
stack depths, interrupts at `n` and records `frontier`; body wrapped in try/catch so a
tracer defect marks the run *invalid*, never pass or fail); `TapeScheduler extends
MixedScheduler` recording `scheduleTask`/`shouldYield`; phase sentinels `build | run |
teardown` from `Effect.sync` at the `provide` boundary, comparison covers `run` only;
`runTraced(program, { tape, budget, maxOpsBeforeYield })`.

Protocol rules: each program runs twice, `MaxOpsBeforeYield` pinned large (primary, must
show zero yields) and at 1 (scheduler-insensitivity check; the two service-level traces must
be identical); snapshots record names and depths, never object identity; every trace file
carries the host pin (effect, upstream `2600f62f…`, tree `aea8ac8a…`, tsc 7.0.2, tsgo 0.38.0,
node, platform, patched: null), tape, scheduler inputs, foreign registrations; no timestamps
or absolute paths. Budget rule: a Lean golden ending in `done` must not hit the host budget;
one ending in `frontier` must. Comparison prints `trace <program>.<tape> mask <m> ok` or the
first differing row with the frame snapshot beside it.

Acceptance: `harness/trace/check.sh` = fixture byte-identical, `effect4-check` four gates,
`effect4-trace` all masks ok; negative: a tail without the Decisions layer fails tsgo with
`missingEffectContext`; self-tests: a planted throwing tracer reports invalid; a pair that
agrees under M1 and not under M2 fails M2.

### P-T4 Goldens (~200 lines scripts)

- Lean-expected traces are deterministic projections: `generated/traces/<program>.<tape>.tsv`
  (header rows format / generator sha256 / regenerate / input sha256 / effects pin / program
  / tape / rules), emitted by `harness/trace/Emit.lean` through `X.traced`; host receipts
  live under `harness/trace/receipts/` (not `generated/`).
- Two gates: `scripts/check-trace-goldens.sh` (hermetic: regenerate from Lean, `cmp`) and
  `scripts/check-trace-host.sh` (node: actual vs expected under each mask, writes receipt);
  `scripts/test-trace-goldens-gate.sh` plants a flipped answer, a stale pin, a removed mask
  row, and (after P-T7) a `try/finally` tail; each must trip a named detector.
- First goldens: `incr.empty`; the tower (`Cell` over `Jobs`, hand-written host layer,
  traced at both faces); a failing-op program after P-T8. Every golden is produced twice in
  Lean once the Flow runner exists (traced service and Flow runner must agree first).
- CI: the hermetic gate always; the host gate fails (never skips) when
  `EFFECT4_EFFECT_NODE_MODULES` is absent.

### P-T5 Lowering coverage ledger (~150 Lean + 200 shell)

- `Effect4/Target/TypeScript/Lower.lean` (stub today): `inductive Rule` with `Rule.id`,
  `Rule.all`, `all_nodup`, `mem_all`; `Script.rules : Script → List Rule`; later `Flow.rules`.
- Numerator `Effect4Test/Target/TypeScript/LoweringCoverage.lean` (exact-module exemption):
  frozen rows `(rule, state, goldens, host, property, typeReceipt, proof)`; elaboration-time
  checks: one row per rule; `proof` resolves to a theorem within the ceiling; declared
  state equals the derived state.
- `scripts/generate-lowering-coverage.sh > generated/lowering-coverage.tsv`,
  `check-lowering-coverage.sh` (drift + both directions: tag without row, row without tag,
  golden path missing or digest drifted, host receipt pin ≠ current pin, `frames.jsonl`
  cited as evidence), `test-lowering-coverage-gate.sh` (five planted mutants with named
  signals). Rule rows also list the runtime-census row ids they rest on (existence-checked
  only; never adds a census witness).

### P-T8 Errors (~250 lines; after P-T5, independent of Flow)

Derive syntax `| op (p : T) : A ! E ⟪…⟫` sets `OpRow.error`; `methodType` renders
`Effect.Effect<A, E>`; expected service kind `X.Service (ExceptT E M)`; `tsOfType` gains
`Except E A → Either.Either<A, E>`; `Emit.lean` appends `done (failure e)`; host proxy records
`failed` from a tapError arm. Goldens: abort reading (trace ends `done failure`), data
reading (`answer` carries `[false,"boom"]`, program continues), `catchTag` restore when `E`
is a tagged inductive. Row `E4-TARGET-CE-` "an `Except` answer rendered as `Effect<A,E>`"
(Lean recovers, host aborts under M1; repair: two row shapes). This packet re-pins
`fixture.ts` (`check.sh --update`, diff reviewed).

### P-T10 Type receipts (~150 lines; any time after P-T4)

Primary, pin-faithful: `tsc.original -p tsconfig.json --declaration --emitDeclarationOnly`
into a temp dir and byte-compare the emitted `.d.ts` with a Lean-rendered expectation
(`ServiceRow.declarationFile`); an `E` or `R` drift is a text diff. Auxiliary: a TypeScript
5.9.3 extractor (`packages/effect-profile/effect-channels.mjs`,
`checker.getPropertyOfType(type, "~effect/Effect")` + variance members) labelled skewed in
its header. Ledger column `typeReceipt` accepts only the primary.

### P-T2' Flow v2 (lean4-effects v0.4.0; ~400 Effects + 300 batteries; largest packet)

Fence: `Effects/Flow/{Block,Raw,Admission,Checked}.lean`; batteries move from
`Effect4Test/Flow/*` to `EffectsTest/Flow/*` (Effect4 keeps thin consumers);
`test/contracts/flow-v2.contract.md` re-freezes `flow-admission`.

```lean
structure Var where index : Nat                       -- position in the block's parameter list
structure RegionId where value : Nat
inductive RawTerm
  | ret (value : Var)
  | jump (target : BlockId) (args : List Var)
  | perform (operation : OperationId) (request : Var) (target : BlockId) (args : List Var)  -- target.params = argTys ++ [answerTy]
  | choose (decision : DecisionId) (left right : BlockId) (args : List Var)
  | enter (region : RegionId) (body : BlockId) (args : List Var)
  | leave (value : Var)                               -- ends the innermost region
structure RegionRow (Ty) where id : RegionId; parent : Option RegionId; finalizer : BlockId; continue_ : BlockId; resultTy : Ty
structure RawBlock (Ty) where id : BlockId; region : Option RegionId; params : List Ty; term : RawTerm
```

New admission clauses: `unknownVariable`, `argumentArity`, `argumentTypeMismatch`,
`regionOwnership` (successors share the region label or are its `continue_`; `leave` only
inside a region; finalizer params `[resultTy]`), and `everyCycleChooses` (each cycle passes a
`choose`, so a finite tape bounds every run and the host cannot loop). Atoms are ordinary
operations flagged `pure` on the Effect4 row (no terminator change; excluded from traces by
mask). Rows: `EF-FLOW-CE-001` "one payload can carry the environment" (repair: params);
`-002` "`leave` may target any region" (repair: innermost only); `-003` "well-bracketing
needs dominators" (repair: static ownership labels now).

### P-T2 Flow runner (Effect4; ~250 lines; after P-T2')

`Effect4/Semantics/Runs.lean` (executable face), `Semantics/Frontier.lean`, `Flow/Decision.lean`
(the tape) — each a stub today, so each needs its packet first.
```lean
inductive Frontier | fuel (at : BlockId) | unansweredDecision (site : DecisionId) | stuck (at : BlockId)
inductive RunResult | done (value : Val) | frontier (reason : Frontier)
structure FlowService (alphabet) (M) where handle : alphabet.Op → Val → M Val; pure : alphabet.Op → Bool
def Flow.run [Monad M] (fuel) (flow : CheckedFlow alphabet) (service) (nameOf) (tape) (input : Val)
  : StateT (List Trace.Event) M RunResult
```
Fuel is `tape.length + blocks.length + 1` (fuel is never the binding frontier when every
cycle chooses). Lemmas: `run_checked_not_stuck` (from admission), `run_fuel_mono`,
`run_choose_consumes_one`. `Script.toFlow` embeds straight-line scripts; golden
`incr.flow.empty` must equal `incr.empty` under M2 (internal oracle). Row `E4-FLOW-CE-`
"fuel exhaustion is a failure" (repair: frontier, DB-04 wording in runner and harness).

### P-T9a Dispatch-form lowering (lean4-typescript v0.2.0 + Effect4; ~350 lines)

`TypeScript/Syntax.lean` `Stmt` gains `letDefinite`, `assign`, `whileTrue`, `switch`,
`ifElse`, `continue_`, `breakTo`, `labelled`, `exprStmt` with renderer arms and byte examples.
`Effect4/Target/TypeScript/Lower.lean`: `Flow.lowerDispatch : ServiceRow → CheckedFlow → Option ProgDecl`
(`const cell = yield* Cell; const decisions = yield* Decisions; let block = entry; let b<i>p<j>!: T; while (true) { switch (block) { case i: {…; block = k; continue} } }`),
`choose` → `if (yield* decisions.choose(site))`, pure ops as calls, block-parameter
passing as a sequentialized parallel move (temporaries only on back edges). The syntax has
no `try` arm, which is R4 by construction. `Flow.rules` feeds the ledger.

### P-T6 Property loop (~300 lines; after P-T9a)

`harness/trace/Property.lean`: seeded LCG in `StateM Nat`, flows generated *by
construction* over the family's type graph (ops whose request type matches the current
payload, `choose` arms typed identically, back-edges only to same-typed blocks, ids strictly
ascending), then `admit` as the free oracle (a refusal is a generator bug); tapes: all-left,
all-right, alternating, seeded random, length ≤ fuel; per-site branch coverage counter (the
gate fails if any site never took both branches). All admitted flows are lowered into ONE
module (`property.fixture.ts` + tapes) and run once with `effect4-trace --batch`; diff under
M2. Shrinking: budgeted (≤64 candidates): truncate tape, replace `choose` by the taken
`jump`, delete a type-neutral `perform`; shrink against the Lean-vs-Lean oracle first, confirm
on the host once; store as first-order data (flow, tape, seed) and as an `E4-TARGET-CE-` row
with a Lean witness and a host fixture. `scripts/test-lowering-mutations.sh` plants three
lowering mutants in a temp copy (swap arms at one site, ignore the tape, off-by-one cursor);
the corpus must catch each or the gate fails. `generated/lowering-property.tsv` records seed,
generated, admitted, frontier counts, digests.

### P-T7 Regions (~350 lines; after P-T6)

Runner semantics for `enter`/`leave`/`finalizer` (innermost first). Two rules with two
Lean checks: `region.onExit` (finalizer sees the *body's* exit; checked against
`Runtime.lean`'s `ranFinalizer`/`restoreAfterFinalizer` shape) and `region.scoped`
(`acquireRelease` inside `Effect.scoped`; all releases see the *closing* exit, LIFO;
checked against `Scope.closeOrder`/`closeExits` on a finite Scope value per golden).
Goldens pin, per finalizer, its position, the exit it observed, and the combined exit after a
finalizer failure: nested `onExit` with body failure; two `acquireRelease` in one scope with
body failure; release 1 fails while release 2 succeeds; both success paths; idempotent
second close. Rows: "region lowered to JS `finally`" (negative golden records the
finally-never-runs fact); "scope finalizer given its region's exit instead of the closing
exit"; "finalizers in registration order"; "finalizer registered during close" (repair:
admission clause, refused not modelled). Refusals: no interrupt cause, no parallel strategy,
no finalizer that performs a region.

### P-T9b Structured form (lean4-typescript `TypeScript/Structure.lean`; ~450 lines; after P-T7)

Re-derived from js_of_ocaml (algorithm below). `Flow.lowerStructured` behind `reducible?`,
fallback dispatch; theorem in Lean that both forms' service-level traces agree on every
flow (pure Lean, provable); ledger rows `loop-labelled`, `merge-block`, `dispatch-fallback`,
plus a reducibility refusal row.

### P-T11 Patched rc.112 copy (phase 2; ~400 lines; last)

`harness/trace/patched/{patch-manifest.json, apply.mjs, trace-host-pin.json}`; hunks at
`getCont` (`dist/internal/effect.js:487-503`), `exitFailCause` handler skipping
(`core.js:321-324`), `scopeCloseFinalizers` (`:1584-1601`), `memoMapBuild`
(`Layer.js:133-178`), emitting `frames.jsonl` rows keyed by census row id. Lean side:
`Simulation.lean` gets `FrameEvent.toTrace` and `Event.toTrace` projections (finalizer and
outcome only) and the FRAMES-DAG bridge row. Only ever selected by
`EFFECT4_EFFECT_NODE_MODULES`.

## Structured lowering algorithm (normative, re-derived; LGPL source is reference only)

1. `norm`: any region entry or function entry that is a jump target gets an empty pre-header.
2. Graph: DFS post-order → RPO; `preds` by reversal; an edge is backward iff `index src ≥ index dst`.
   For each region `(enter, continue_)` add the artificial edge `enter → continue_` so the
   post-region block is a sibling scope, not nested in the region.
3. Dominators: Cooper–Harvey–Kennedy over forward edges; if the fixed point fails the
   graph is irreducible → dispatch form only.
4. `shrinkLoops`: for each non-small block that leaves a loop, add edges from the loop
   header's forward predecessors to it (post-loop code lands outside the loop).
5. Emit with a scope stack (`Loop | Exit_loop | Forward | Dispatch`) and `fall_through` /
   `never` bookkeeping: loop header → labelled `while (true)`; dominator children that are
   merge nodes (or ≥2 decision-tree leaves) → labelled blocks in descending RPO, falling
   through in order; more than 10 siblings → selector `switch` in a loop; any other target
   inlined at its single use; a region end emits nothing.
6. Block parameters: sequentialized parallel move; temporaries only on back edges.

## What agreement does not establish (refusal rows in the ledger)

Semantic preservation beyond the corpus; anything about primitives or frames; interruption;
concurrency and scheduler order; types (separate receipt); layer build, memoization and
provided-scope semantics (phase sentinel); host error identity, stack annotations, `Die`
payloads; termination (frontiers compare as frontiers); byte identity of the program
(separate drift gate); any statement about the host from a Lean theorem.

## Conventions checklist (every packet)

Claim rows first; contract + battery + `known-red.txt` during the red phase (both repos;
see D2); root imports; exact-module `Classical.choice` entries for rendering, emitters and
drivers (semantic modules stay `String`-free); generated receipts with drift gate and
mutation self-test; harness pin, tape, scheduler inputs, foreign registrations; no
line-numbered citations into the routers (`check-internal-citations.sh`); lean4-typescript
gets `AGENTS.md`, a gate and `test/` in P-T9a.

## Order and estimates

```
P-T0 → P-T1 (Effects v0.3.0) → P-T1b → P-T3 → P-T4 → P-T5 → P-T8
                                                  └→ P-T10 (parallel)
P-T2' (Effects v0.4.0, after P-T5 green) → P-T2 → P-T9a (typescript v0.2.0) → P-T6 → P-T7 → P-T9b → P-T11
```

| Step | Packets | Days | Exit |
| --- | --- | --- | --- |
| 1 | P-T0, P-T1, P-T1b | 2 | traced `incr` and tower traces from Lean; gates green |
| 2 | P-T3, P-T4 | 2 | host traces agree with goldens under M1 and M2; both drift gates |
| 3 | P-T5, P-T10, P-T8 | 2 | ledger gate; type receipts; error goldens |
| 4 | P-T2', P-T2 | 3–4 | Flow v2 admitted; runner agrees with traced service on `incr` |
| 5 | P-T9a, P-T6 | 3 | property batch (200 flows × 4 tapes) agrees; mutants caught |
| 6 | P-T7 | 2–3 | region goldens; finalizer exits pinned against Scope |
| 7 | P-T9b, P-T11 | 3 | structured = dispatch on all traces; patched host for pop order |

## Verification

- lean4-effects: `lake build` (gate), `scripts/check-algebra-parity.sh`, `scripts/test-trust-gate.sh`.
- lean4-effect4: `lake build Effect4`, narrow batteries via `lake env lean -DmaxErrors=10000`,
  `scripts/test-trust-gate.sh`, `check-trace-goldens.sh`, `check-trace-host.sh`,
  `check-lowering-coverage.sh`, `check-lowering-property.sh`, `check-lowering-types.sh`, each
  with its `test-*-gate.sh` planted mutants, `check-internal-citations.sh`.
- Host: `harness/trace/check.sh` (fixture drift, four host gates, all masks), `effect4-trace --batch`.
- End to end: a golden change in Lean must fail the host gate until the receipt is
  regenerated, and a host receipt with a different pin must fail the ledger gate.

## Decisions (ruled by the operator, 2026-09-02)

- **D1 Flow v2 lands after the Script pipeline** (step 4), as Effects v0.4.0 in one bump.
- **D2 Ceremony is light everywhere except P-T2'.** For every packet but the Flow v2
  re-freeze, the builder writes contract, battery and code in one commit and the known-red
  phase is skipped; P-T2' keeps the separate breaker process because it re-freezes the
  `flow-admission` contract.
- **D3 P-T0 pushes.** Push lean4-effects v0.2.0, create and push
  `pure-algebra/lean4-typescript` and `pure-algebra/effect4-tools` (public, MIT), then
  `lake update` and commit the manifests in Effect4 and whatwg; retire the path overrides.
