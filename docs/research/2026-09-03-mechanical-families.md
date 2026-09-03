# Can the remaining host semantics be covered mechanically by traced families?

Research report, 2026-09-03. Read-only survey; no library code, contract, pin, ruling or
generated fact changed. Citations are file:line at HEAD `5af27c4`.

## Verdict

**Mechanically *emitted*: yes. Mechanically *covered*: no, and the gap is not in the
harness.**

`effect_signature` already turns one declaration into a family, a service class, host rows,
wire encoders and a traced service (`Effect4/Meta/Derive.lean:180-204`), so writing a
`Scopes` or `Interrupts` family is cheap. But three of the operator's premises do not hold
against the tree, and each one bounds what mechanisation can buy:

1. **Coverage is defined as a Lean theorem per census clause.** `docs/RUNTIME-COVERAGE.md`
   ("Witness": a Lean `theorem`, frozen by `#check` ascription, receipt inside
   `propext`/`Quot.sound`; "A finite probe, a compile, a test ... does not turn a clause
   green"), and `docs/LOWERING-COVERAGE.md:10-11` says it in one line: *"a host trace never
   turns a census row green."* That is ruling R8. **No packet below moves the metric.**
2. **Ref, Deferred, Layer build and Layer memoisation are not reified.**
   `Effect4/Stateful/Ref.lean`, `Stateful/Deferred.lean`, `Layer/Memo.lean`,
   `Layer/Build.lean`, `Runtime/Resource.lean`, `Runtime/ManagedRuntime.lean` and
   `Runtime/Lifecycle.lean` are each 8-line breadth stubs with zero declarations. There is
   also no `ref.*`, `deferred.*` or `layer.*` **kind** in the census
   (`Effect4Test/Audit/RuntimeCoverage.lean:2566-2568`: `op, frame-arm, checkpoint,
   interrupt, fork, scope, scheduler, exit, cause, entry, rule`), so a golden for them would
   witness nothing and could not even *cite* a row. (Latent bug:
   `harness/trace/patched/patch-manifest.json` gives the `layer.memo-build` hunk
   `"census": "layer"`, which is not a census kind.)
3. **The census is 99 rows, not 97.** `grep -c '^mechanism' generated/effect-runtime-census.tsv`
   = 99; `expectedRowTotal := 99`, `expectedDenominator := 79`
   (`RuntimeCoverage.lean:3818-3819`); 49 green, 25 partial, 25 absent, 20 excluded.
   Of the 25 absent rows only five are in the denominator (`op.Yield`, `op.Async`,
   `checkpoint.runloop-top`, `checkpoint.post-yield-cancel`, `rule.yield-is-overloaded`);
   the other twenty are `targetOnly`/`excludedInternal`. **The metric's headroom is 25
   partial rows plus five absent ones, and every partial row's missing clause is a *model*
   gap, not an evidence gap.** Read them: `scope.close-sequential` "is temporal sequencing, a
   fiber-machine fact" (`:3071`), `scope.close-parallel` "is a fiber-machine fact" (`:3078`),
   `scope.fork-linkage` "needs a scope store" (`:3095`), `scope.scoped` "installs a fresh
   scope in the fiber context" (`:3106`), `scope.acquire-release` "needs a Context carrier"
   (`:3123`), the `fork.*` rows "See SUPERVISION-PG-RC112".

So the honest framing: **traced families mechanise the falsification budget and the lowering
ledger, not the runtime-coverage metric.** They are still worth building. Of the 79
denominator rows, the 49 green ones have a Lean theorem and almost no host observation
whatsoever; the only model facts a host has ever confirmed are three scope facts pinned by
`scripts/check-trace-patched.sh`. A divergence between `Scope.close` and rc.112, or between
`InterruptMask` and the real mask frame, would currently go undetected. That is the product.

## 1. The signatures, per reified structure

### What the DSL admits today

`tsOfTypeFuel` (`Derive.lean:72-96`) admits `Nat | Int | String | Bool | Unit` and
`Option`/`List`/`Except` over them, and nothing else; an unknown identifier is a hard error
("add a Stratum V row first", `:81`). Op names must satisfy `TypeScript.targetIdentifier`
(`:142-143`), so `close-again` must be spelled `closeAgain`. `effect_program` is
straight-line only: `let x <- Fam.op(args)` and `return` (`:229-264`).

**Two genuinely new features are needed; one is not.**

- **An op that takes a scope (or a ref, a fiber, a deferred) is new.** There is no handle
  spelling. Minimal change: admit one opaque `Handle` type whose Lean carrier is `Nat` (so
  `ToVal` and `DecidableEq` come free) and whose TypeScript spelling comes from a per-family
  override alongside `OpRow.tsParams` (`Effect4/Target/TypeScript/EffectV4.lean:41-54`).
  `Effect4/Foreign/Registry.lean` is the existing home for a registered foreign name. Roughly
  40 lines in `Derive.lean` plus one row field; no alphabet change, because the wire value
  stays a `nat`.
- **An op whose answer is an `Exit` is new, and it is the section 4 defect in disguise.**
  `Effects.Trace.Outcome` (`lean4-effects/Effects/Trace.lean:62-66`) is `success | failure |
  interrupted`; it is *not* a `Val`, has no `ToVal` instance, and `tsOfType` cannot spell it.
  The cheap approximation `Except String Unit` (already spelled `Result.Result<void,
  string>`) drops `interrupted` and drops defects entirely. Do section 4 first.
- **A handler stateful across ops is already supported; no feature needed.**
  `Family.Service F M = (name : F.Name) -> F.Param name -> M (F.Answer name)`
  (`lean4-effects/Effects/Family.lean:39`), so `M := StateT (Scope kappa phi ...) Id` threads
  scope state, and `X.traced` composes to `StateT Log (StateT S Id)` (`Derive.lean:196-198`).
  The real constraint is data, not syntax: `Scope.close` takes its `run : phi -> Exit -> Exit
  Unit ...` as a parameter (`Effect4/Runtime/Scope.lean:807`), so the handler must fix `phi :=
  Nat` and carry a finalizer table.

### The families worth writing

| Family | `effect_signature` (sketch) | Lean model handler wraps | Host implementation | Census rows it may **cite** |
| --- | --- | --- | --- | --- |
| `Scopes` | `make (parallel : Bool) : Nat`; `addFinalizer (scope key : Nat) : Unit`; `removeFinalizer (scope key : Nat) : Unit`; `close (scope : Nat) (ok : Bool) : Except String Unit` | `Scope.make` (`Scope.lean:241`), `Scope.addExit` (`:613`), `Scope.removeUnsafe` (`:672`), `Scope.close`/`closeResult`/`closeOrder`/`closeExits` (`:807`, `:796`, `:785`, `:790`) | rc.112 `Scope.makeUnsafe`, `addFinalizerExit`, `Scope.close` | `scope.make`, `scope.add-finalizer`, `scope.add-after-closed`, `scope.remove-finalizer`, `scope.close-state-first`, `scope.close-lifo`, `scope.close-sequential`, `scope.exit-as-void-all`, `rule.scope-close-lifo-state-first` (9) |
| `Interrupts` | `deliver (site : Nat) : Bool`; `enterMask : Unit`; `exitMask : Unit` | `InterruptMask` (`Concurrency/Interrupt.lean:16-19`), `FrameFiber.getCont` (`Runtime/Runtime.lean:1181`), `ensure_setInterruptible_substitutes` (`:657`) | `Effect.withFiber(f => f.interruptUnsafe())`, `Effect.uninterruptible` | `interrupt.unsafe-entry`, `interrupt.accumulate`, `rule.record-and-apply-separate`, `rule.interrupt-bypasses-handlers`, `checkpoint.getcont-deferred`, `checkpoint.exit-failcause-skip`, `op.OnExit`, `frame-arm.OnExit`, `frame-arm.SetInterruptible` (9) |
| `Fibers` | `fork (uninterruptible daemon : Bool) : Nat`; `join (fiber : Nat) : Except String Nat`; `awaitExit (fiber : Nat) : Except String Nat`; `interrupt (fiber : Nat) : Unit` | `Supervision.forkUnsafe`/`forkChild`/`forkDetach` (`Supervision.lean:244`, `:274`, `:280`), `Fiber.observe`/`publish`/`recordInterrupt` (`:195`, `:212`, `:223`), `MaskMode.select` (`:119`) | `Effect.forkChild`, `Effect.forkDetach`, `Fiber.join`, `Fiber.await`, `Fiber.interrupt` | the twelve `fork.*` rows, `rule.only-fork-child-tracks`, `rule.children-interrupted-after-exit` (14) |
| `Refs`, `Deferreds`, `Layers` | -- | **nothing exists** | -- | **none: no census kind** |

Two notes on `Fibers`. First, nine of these facts are *already* observed on the host by
`harness/fiber-supervision/runtime-check.ts` (171 lines of bespoke asserts: daemon cleanup
runs exactly once, `await` value distinct from `join` effect, a parent interrupt during a
child wait replaces the body success and retains interruptor id 99, and so on). The
mechanical win is re-expressing those nine assertions in the shared alphabet, so they become
goldens a Lean face must reproduce rather than a script only a human reads. Second, `Scopes`
and `Interrupts` can be reached through the *existing* region path
(`Effect4/Flow/Region.lean`) without touching `effect_program`; `Fibers` cannot, because the
region runner is single-threaded by construction.

## 2. Interruption as decisions (R6)

**The shape already exists.** `Decisions` on the host is `choose(site) : Effect<boolean>`
answered from a tape by occurrence with a site check (`harness/trace/tracer.ts:101-119`:
exhaustion gives `TapeExhausted` and a `frontier` row; a mismatch gives `TapeSiteMismatch`, a
refusal). `Effect4/Flow/Decision.lean` is the Lean tape. An `Interrupts` family is the same
protocol with a different question: *is the interrupt delivered at this interruptible point?*

**What the Lean side has, and where.** Mask semantics exist in two disconnected models. The
scheduler machine proves `masked_interrupt_defers` (`Concurrency/Scheduler.lean:2068`),
`unmask_delivers_pending` (`:2091`), `unmasked_interrupt_delivers` (`:2044`). The frame
machine proves the runtime facts: `getCont_deferred` (`Runtime/Runtime.lean:1193`),
`interrupt_skips_every_handler` (`:1559`), `getCont_mask_stops_skip` (`:1578`),
`ensure_onExit_masks` (`:612`), which is the census's `frame-arm.OnExit` clause that the
finalizer runs masked.

**What it does not have, and this is the blocker.** *No Lean emitter can produce
`Outcome.interrupted`.* The only construction of it in the tree is
`Simulation.Exit.toOutcome` (`Effect4/Target/TypeScript/Simulation.lean:38-42`), the P-T11
bridge, which never feeds a golden. The region runner's result alphabet has no interrupt at
all, and its contract says so: *"Refusals (not modelled): an interrupt cause, a parallel
finalizer strategy..."* (`test/contracts/flow-regions-runner.contract.md:37`). So the first
packet is Lean-side: `RunResult.interrupted`, `closeFrame` closing open frames with
`Outcome.interrupted`, and `deliver` consuming a tape entry.

**Host injection is nearly free.** `runTraced` already interrupts a real fiber at a counted
primitive: `if (primitives > options.budget) { sink.push({kind:"frontier"});
fiber.interruptUnsafe() }` (`tracer.ts:165-170`). Moving that call behind a service method
(through `Effect.withFiber`) makes the site *nameable* and lets the tape decide, which is
exactly R6. The patched row `frame.deferred-interrupt`
(`harness/trace/patched/patch-manifest.json`) then records the `getCont` answer beside it as
frame evidence, recorded and never compared.

**A defect found while reading.** The budget path has no latch: `primitives` keeps rising, so
every primitive after the budget pushes another `frontier` row (`tracer.ts:167-169`), whereas
a Lean frontier is a single row. No golden hits the budget today (default 100000,
`tail.ts:18`), so the first interrupt golden will be the first to trip it. Fix with a one-line
guard before any interruption work.

**What stays refused.** The wire drops the interruptor id: `Outcome.interrupted` renders
`{"interrupted":true}` (`Effect4/Target/TypeScript/Trace.lean:44`), and TRACE-DAG separation
3 makes the outcome annotation-blind and host-error-identity-blind by decision. So
`cause.reason-interrupt`'s clause "carries an optional interruptor fiber id" is
**unwitnessable by any trace under `m1` or `m2`**; the existing `runtime-check.ts` assertion
about `fiberId === 99` is strictly stronger than anything this lane can say. Also refused: an
interrupt cause inside regions (the contract line above), and, until section 4, telling a die
from a failure.

## 3. Scheduling as decisions

**What exists.** `SchedulerDecision` has seven constructors, `schedule`, `join`,
`requestInterrupt`, `enterMask`, `exitMask`, `complete`, `cleanup` (`Scheduler.lean:22-30`);
`DecisionTape tau := List (SchedulerDecision tau)` (`:32`); `Event tau` has ten (`:35-47`);
`Runs` replays a tape (`:632`); `step_deterministic` (`:1499`) and `fixedTape_deterministic`
(`:1696`) are proved. The plan's `scheduleTape` (`misty-frolicking-naur.md:54`) is not an
identifier in the tree; the object is `DecisionTape`.

**What the `TapeScheduler` actually is.** It decides nothing. It is a `MixedScheduler`
subclass that overrides `shouldYield` and increments a counter (`tracer.ts:151-157`); the
`scheduled: number[]` field is documented as "priorities are recorded once the dispatcher is
instrumented (P-T11)" and is still empty (`:146`). Calling it a decision source overstates it
by a wide margin.

**What single-fiber to two-fiber needs.** The host side is small: `Effect.forkChild` behind a
`Fibers` method, plus a `shouldYield` that reads a tape instead of counting; `shouldYield` is
the one hook the pinned `Scheduler.ts` exposes (`scheduler.should-yield`,
`Scheduler.ts:174-176`). The Lean side is not an extension but a packet: `Machine = { fibers :
List (FiberState tau), trace }` (`Scheduler.lean:64-67`) and `FiberState`
(`Concurrency/Fiber.lean:58-65`) carry **no program**, so the machine cannot emit an `op`
event at all, and `Simulation.Event.toTrace` projects only completions to outcomes
(`Simulation.lean:56-59`). A two-fiber service-level trace therefore requires attaching a
`Program`/`Flow` to each `FiberState`: a new model, comparable in size to the frame machine.

**Scheduler insensitivity as a theorem.** On the Lean side it is today *vacuous*: the emitters
are `StateT Log Id` with no scheduler parameter, so there is nothing to be insensitive to. The
property actually checked lives in the protocol (TRACE-DAG separation 8: every golden runs at
a large `MaxOpsBeforeYield`, requiring zero yields, and at the rc.112 floor of 3, with
identical service-level rows). The theorem worth owing, once fibers carry programs, is a
**permutation** law strictly stronger than `fixedTape_deterministic`:

> for tapes `t1`, `t2` that induce the same per-fiber decision order, `Runs boundary m t1 r1`
> and `Runs boundary m t2 r2` give `project mask (trace r1) = project mask (trace r2)`.

It needs a per-fiber projection of `Trace tau`, which `Event.cleanupId?`
(`Scheduler.lean:50`) gestures at and nothing supplies.

## 4. Defects and the wire

| # | Defect | Exact citation | Minimal change | Bump |
| --- | --- | --- | --- | --- |
| i | A **die renders as `{"failure":[]}`**, not `{"failure":undefined}`: `reasons.find(r => r._tag === "Fail")` is `undefined`, and `wire(undefined)` returns `"[]"` (`tracer.ts:35`). A defect is therefore byte-identical to `failure unit`; and a `Die` accompanied by an `Interrupt` renders `{"interrupted":true}`, because line 69 excludes only `Fail`. Lean cannot spell a defect either: `Outcome` is `success \| failure \| interrupted`. | `tracer.ts:65-72`; `Effects/Trace.lean:62-66` | **Now:** `outcomeWire` throws `TracerDefect` when the cause carries neither `Fail` nor `Interrupt`, so the run is marked *invalid*, never silently equal (two lines). **Then:** add `Outcome.defect (payload : upsilon)`, rendered `{"defect":v}`. | invalid-marking: none. `Outcome.defect`: **lean4-effects v0.6.0** (the alphabet is frozen by `EffectsTest/Trace/TraceContract.lean` and `test/contracts/trace.contract.md`), an Effect4 pin bump, one new arm in `Trace.outcome` and in `outcomeWire`. `Mask` needs no new flag. No golden re-pin: no golden dies today. |
| ii | **`Val.nat` and `Val.int` render identically** (`toString n` / `toString i`), so equal rendered rows do not imply `agree m2`: the host gate compares rows, not events. | `Effect4/Target/TypeScript/Trace.lean:33-34`; Codex `E4-TARGET-CE-011` (`docs/research/2026-09-02-effect4-of-ocaml-review/integration-review.md:46`) | Do **not** change the wire. State the gate as agreement *under the declared answer-type profile*, which the host already honours (`wireAnswer`, `tracer.ts:76-77`), as TRACE-DAG separation 9; and refuse `Int` in trace-lane signatures until a spelling separates them (`tsOfType` maps both to `number`, `Derive.lean:77`). | none |
| iii | **A C0 control is not escaped.** `escape` handles only `"`, `\`, newline, carriage return and tab; U+0001 passes through raw, `JSON.parse` rejects the cell, and the host's `JSON.stringify` (`tracer.ts:41`) emits a six-character escape, so the two faces disagree on a legal `String`. | `Effect4/Target/TypeScript/Trace.lean:24-29` | Escape every character below 0x20 as `\uXXXX` in `escape`; nothing to mirror, since `JSON.stringify` already conforms; plant the character in `scripts/test-trace-goldens-gate.sh`. | none (the renderer is an exact target-implementation module, and no golden contains a control character) |
| iv | **Naturals above 2^53 - 1 lose precision** on the host; `wire` guards `Number.isInteger` only. | `tracer.ts:36-39`; Codex `E4-TARGET-CE-013` | `if (!Number.isSafeInteger(value)) throw new TracerDefect(...)`, plus an admission clause on golden emission in `harness/trace/Generate.lean` (magnitude at most 2^53 - 1). | none |

Recommended order: iii and iv first (each one line, no bump, each testable by a planted
mutant), then i's invalid-marking, then `Outcome.defect` as the only alphabet change, and
only if an interruption packet actually needs to distinguish a defect, which the `Interrupts`
family does the moment a finalizer can die.

## 5. Packets

Ranked by *census rows given their first host observation per day*. **None moves the
runtime-coverage metric**; each says so in its refusals, per R8.

### P-M0 -- Wire hardening (0.5 d; blocks everything)

*Fence:* `Effect4/Target/TypeScript/Trace.lean` (`escape`), `harness/trace/tracer.ts`
(`wire`, `outcomeWire`), `harness/trace/Generate.lean` (golden admission),
`scripts/test-trace-goldens-gate.sh`, `docs/TRACE-DAG.md` (separation 9).
*Declarations:* none new. *Evidence:* three planted mutants -- a raw U+0001, a natural above
2^53 - 1, a dying program -- each tripping a named detector. *Refusals:* `Val.nat` and
`Val.int` stay non-injective, recorded as separation 9 and a new `E4-TARGET-CE-` row; no
census row moves. *Rows cited:* 0.

### P-M1 -- Frontier latch and the first budget golden (0.5 d)

*Fence:* `harness/trace/tracer.ts` (`runTraced`), `harness/trace/receipts/`.
*Declarations:* none. *Evidence:* a golden whose Lean face ends in exactly one `frontier` and
whose host run hits the budget; it fails against today's code (`tracer.ts:167-169` emits one
`frontier` per primitive past the budget) until latched. *Refusals:* a budget frontier is not
an interrupt outcome and never compares as one (TRACE-DAG separation 5). *Rows cited:* 0.

### P-M2 -- `Scopes` traced family (1.5 d; needs the handle spelling)

*Fence:* `Effect4/Meta/Derive.lean` (handle spelling and row override),
`harness/trace/scope-fixture.ts` (generated), `scope-tail.ts`, `harness/trace/Generate.lean`,
`generated/traces/scope/*`, `harness/trace/receipts/scope/`.
*Declarations:* `effect_signature Scopes`; a handler over `StateT (Scope Nat Nat ...) Id`
wrapping `Scope.make` / `addExit` / `removeUnsafe` / `close` (`Scope.lean:241`, `:613`,
`:672`, `:807`); goldens for LIFO close, add-after-closed, remove, and an idempotent second
close (`close_idempotent`, `:880`; `close_twice`, `:890`).
*Evidence:* host runs against rc.112 `Scope.makeUnsafe` / `addFinalizerExit` / `close`, under
every mask at both yield settings, with the patched copy's `scope.close-*` hunks recorded
beside them. *Refusals:* the parallel strategy (needs a fiber machine,
`RuntimeCoverage.lean:3078`); fork linkage (needs a scope store, `:3095`); **no census row
moves, because the four `scope.*` partials' missing clauses are fiber-machine and store facts,
not observations.** *Rows cited:* 9, of which 8 get their first host observation.

### P-M3 -- `Interrupts` decision family (2 d; after P-M0 and P-M1)

*Fence:* `Effect4/Flow/Region.lean` (`RunResult.interrupted`, `closeFrame` with
`Outcome.interrupted`), `Effect4/Flow/Decision.lean` (a reserved site range or a second tape),
`harness/trace/tracer.ts` (an `Interrupts` service over `Effect.withFiber`),
`harness/trace/flow-tail.ts`, `test/contracts/flow-regions-runner.contract.md` (re-freeze: the
interrupt refusal is lifted).
*Declarations:* `interrupts_deliver_at_site`; a region-level `mask_defers` mirroring
`masked_interrupt_defers` (`Scheduler.lean:2068`); `finalizer_sees_interrupted` mirroring
`ensure_onExit_masks` (`Runtime.lean:612`).
*Evidence:* three goldens -- unmasked delivery, masked defer then delivery at unmask, a
finalizer observing `interrupted` -- each agreeing at both yield settings, with the patched
`frame.deferred-interrupt` and `frame.exit-fail-cause.skip` rows recorded and never compared.
*Refusals:* the interruptor id is dropped by the wire (TRACE-DAG separation 3), so
`cause.reason-interrupt`'s id clause is unwitnessable here; no census row moves;
`checkpoint.post-yield-cancel` and `op.Yield` stay absent, since no Lean emitter parks.
*Rows cited:* 9.

### P-M4 -- `Fibers` family and the two-fiber host (3 d; largest, after P-M3)

*Fence:* `harness/trace/fiber-fixture.ts`, `fiber-tail.ts`, a tape-driven `shouldYield` in
`tracer.ts`, retirement of `harness/fiber-supervision/runtime-check.ts` into goldens.
*Declarations:* a host `Fibers` service (fork, join, await, interrupt); a Lean handler over
`Supervision` (`forkUnsafe` `:244`, `observe` `:195`, `publish` `:212`, `recordInterrupt`
`:223`). *Evidence:* the nine assertions of `runtime-check.ts` re-expressed as goldens.
*Refusals:* the Lean scheduler emits no service-level interleaving (`Machine` carries no
program, `Scheduler.lean:64-67`), so the Lean face for two fibers is a *sequential* projection
only; scheduler insensitivity stays a host protocol, not a theorem; no census row moves.
*Rows cited:* 14 -- the best rows per day of the four, and the worst rows per unit of risk,
because its Lean face is the weakest.

### P-M5 -- The theorem packets (the only metric movers; not costed here)

One per named missing clause, in `Effect4/` and not in the harness: a Context carrier for
`scope.acquire-release` (`:3123`), a scope store for `scope.fork-linkage` (`:3095`), the frame
machine's `OnExit` chain for `scope.close-sequential`'s sequencing clause (`:3071`), and the
`SUPERVISION-PG-RC112` clauses behind the twelve `fork.*` rows. P-M2 through P-M4 make each of
these falsifiable before it is proved, which is their argument for going first.

### P-M6 -- Refused for this lane

`Refs`, `Deferreds`, `Layers`. No Lean model (8-line stubs), no census kind, and layer build
and teardown are outside the compared window by TRACE-DAG separation 6. Prerequisites, in
order: a census re-pin adding `ref.*` / `deferred.*` / `layer.*` rows through
`scripts/generate-effect-runtime-census.sh` (`docs/RUNTIME-COVERAGE.md`: "Adding or re-pinning
a census row happens in the generator only"), then one model packet each. Fix
`patch-manifest.json`'s `"census": "layer"` in passing, or document it as a non-census label.
