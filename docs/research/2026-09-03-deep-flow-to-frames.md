# The deep compile: first-order Flow into the rc.112 frame machine

Status: research, 2026-09-03. Read-only survey plus one elaborated statement-shape
probe. Nothing under `Effect4/`, `Effect4Test/`, `test/` or `generated/` was changed.

## Summary

1. The compile already exists and is not the two-constructor stub: `Effect4/Semantics/RegionSimulation.lean:312` compiles `ret`, `jump`, `perform`, `performCatch`, `choose`/`branch`, `enter`, `acquire` and `leave` into `Prim`; `Effect4/Semantics/FrameSimulation.lean:195` is only its straight-line ancestor.
2. What is missing is not coverage of the term list but three specific repairs, and a general theorem: `regions_simulate` is prose in a docstring (`Effect4/Semantics/RegionSimulation.lean:109-121`), not a Lean declaration.
3. Repair 1, and the root of `E4-TARGET-CE-019`: the compile emits one `Prim.onExit` **per acquire** (`RegionSimulation.lean:383-385`), so an earlier release sees an exit already merged with a later release's failure via `Exit.restoreAfterFinalizer` (`Effect4/Semantics/Exit.lean:54-68`); rc.112 registers every release into **one** `Scope` closed with `exitAsVoidAll` (`vendor/…/internal/effect.ts:3826, 2025-2038`), which hands every finalizer the same original exit — exactly what `Effect4.Flow.closeReleases` does (`Effect4/Flow/Region.lean:134-145`). The runner is right and the compile is the outlier.
4. Repair 2, `E4-TARGET-CE-020`/`-021`: eight arms of `compileRegion` send a live frontier (fuel 0, stuck block, exhausted or mismatched tape) to `Prim.failure Cause.empty`, whose `Exit.toOutcome` is `.interrupted` (`Effect4/Target/TypeScript/Simulation.lean:37-42`), so the machine finalises work the runner keeps live — a DB-04 violation, not a payload disagreement.
5. Repair 3: `performCatch` compiles to `onSuccess` with the error handled inside `contA` (`RegionSimulation.lean:328-330, 374-377`), while `Effect.result` builds `OnSuccessAndFailure` (`effect.ts:3417-3420, 3450-3460`); `Prim.onSuccessAndFailure` exists and is never emitted.
6. The plan's stated blocker, "the cause-merge divergence (`closeFrame` keeps the first failure)", is **stale**: packet D2 made `closeFrame` keep the merged list (`Effect4/Flow/Region.lean:446-453`) and `FrameSimulation.lean:566-590` records the ruling.
7. `PrimInterp` is pure and total (`Effect4/Runtime/Runtime.lean:191-215`); a point-keyed answer tape stays adequate with regions and catches **provided the service is stateless** — `statelessOracle` (`RegionSimulation.lean:419`) is that hypothesis, and it is the same one D2's `closeFrame_failure_closeResult` (`Region.lean:463-466`) already carries. No state slot is needed, and adding one would re-freeze `test/contracts/frames.contract.md`.
8. Two theorem statements for the general compile — the trace equation and the exit equation — were written out and **elaborate** against the built library (probe, `sorry`-ed); their text is in §2.
9. `ScopeMachine` is the single-scope close done correctly: `request_uses_original` (`Effect4/Runtime/ScopeMachine.lean:100`) is `E4-TARGET-CE-019`'s repair in miniature, and `runState_complete`/`runState_restore` (`:191`, `:217`) are `Scope.closeExitsM` and the exact restoration policy.
10. `ScopeRestoration.resumeClosedScope_complete` (`Effect4/Runtime/ScopeRestoration.lean:81`) is the step law the repaired compile needs: it is exactly "a completed close becomes one `FrameFiber.step`". The general compile should **reuse** both, not subsume them.
11. Their census tags are the `scope.close-*` rows, not `scope.scoped`/`scope.acquire-release`; the two `scope.*` rows stay `partial` for a reason no compile packet touches — a fiber `Context` (`docs/FRAMES-DAG.md:252-253`, `docs/SCOPE-DAG.md:146-147`).
12. T4 should stay at the `Program` face (`Effect4/Target/TypeScript/StructureSemantics.lean:1219`): comparing two skeletons at `Prim` is strictly weaker and drags in an oracle hypothesis T4 does not need.
13. A general compile closes the *settled* half of `docs/TRACE-DAG.md`'s `frame-simulation` row; it cannot close `bridges` (no Lean statement reaches the host) and does not close `structured-agreement`'s open items, which are `Skeleton.denote` gaps.
14. Severity order of the obstacles: scope/frame structure mismatch, frontier finalisation, `performCatch` shape, `Cause.combine` dedup versus `asVoidAll` concatenation, `PrimInterp` purity, interrupt identity, the `Effect.gen`/`Iterator` gap, service lookup. Only the last three need a named refusal rather than a repair. One obstacle the brief assumes is absent: `Effect.interruptible` is emitted nowhere in the repository — masking is one-sided (`Effect.uninterruptible` only) and interrupt points are a service call, `interrupts.point(site)`.
15. Six packets, ~2 100 Lean lines total, of which one (the finite-prefix relation, ~500) is the register's actual demand and the rest are prerequisites.

---

## 1. The term-to-primitive map

Legend for the last column: **=** the three columns agree; **≠** (b) and (c) disagree;
**∅** rc.112 builds no primitive here, or `Prim` has no constructor.

All `effect.ts`/`core.ts` line numbers are in
`vendor/effect-4.0.0-rc.112/src/internal/`. All rule ids are
`Effect4.Target.EffectV4.Rule.all` (`Effect4/Target/TypeScript/Lower.lean:103-110`,
29 entries, `all_nodup` at `:112`); ledger states are
`generated/lowering-coverage.tsv` rows 10–38.

| Flow term / rule (ledger state) | (a) emitted TypeScript | (b) rc.112 primitive | (c) `Prim` constructor emitted by the compile | |
| --- | --- | --- | --- | --- |
| `ret` / `flow-ret` (covered), `ret` (checked) | `return b5p3` — `SkeletonRender.lean:117`; script form `EffectV4.lean:367-369` | generator return, folded by the `Iterator` driver's `[contA]` — `effect.ts:1362-1375`; the value becomes `Success` — `core.ts:509-511` | `Prim.success value` — `RegionSimulation.lean:323`, `Runtime.lean:95` | = |
| `jump` / `param-move`, `block-case`, `dispatch-loop` (covered) | `b3p0 = r1; block = 3; continue` inside `while(true) switch` — `SkeletonRender.lean:85-91`, `Skeleton.lean:234-263` | none — plain JS control flow | none: `compileRegion` recurses — `RegionSimulation.lean:324` | ∅ (agree by construction) |
| `perform` / `flow-perform`, `perform-call`, `perform-bind`, `nullary-value`, `perform-tuple` (covered / checked / pinned) | `const a1 = yield* cell.get` / `cell.put(b1p2)` — `SkeletonRender.lean:96-97`, `Skeleton.lean:267-269`, `SkeletonRender.lean:63-73` | `yield*` inside `Effect.gen` is the **`Iterator`** frame re-pushing itself — `effect.ts:1360-1375`; the service method itself is host code, typically `Sync` (`effect.ts:930`) or `Success` (`core.ts:509`) | `Prim.onSuccess (Prim.sync point) (RegionName.cont point)` — `RegionSimulation.lean:326-327` | **≠** — the compile models one `yield*` bind as `OnSuccess` over `Sync`; rc.112 drives it through `Iterator`. `Prim.iterator` exists (`Runtime.lean:107`) and is never emitted. |
| `performCatch` / `perform-catch` (pinned) | `const a1 = yield* Effect.result(cell.op(x)); if (Result.isSuccess(a1)) {…} else {…}` — `SkeletonRender.lean:107-111`, `Skeleton.lean:289-297` | `Effect.result` = `matchEager` → `matchCause` → `matchCauseEffect` = **`OnSuccessAndFailure`** — `effect.ts:3417-3420`, `3450-3460` | `Prim.onSuccess (sync) (cont)`; the error is answered inside `regionInterp.contA` — `RegionSimulation.lean:328-330`, `374-377` | **≠** — `Prim.onSuccessAndFailure` (`Runtime.lean:113`) is the right constructor and is not emitted; `armE` never runs, so the caught failure is never a `Cause` on the machine side. |
| `choose` / `choose-if` (covered) | `const c0 = yield* decisions.choose(7); if (c0) {…} else {…}` — `SkeletonRender.lean:104-106` | a service method through `yield*`: `Iterator` plus whatever the host service builds | none: `compileRegion` recurses on the branch the tape already fixed — `RegionSimulation.lean:331`, `Runs.lean:176-184` | **≠** — the host performs an operation where the compile performs none. Masked out of the compared trace: `finalizerAndOutcomeMask` sets `decisions := false` (`RegionSimulation.lean:208-210`). |
| `branch` / `branch-if` (pinned) | `yield* decisions.report(7, b1p0); if (b1p0) {…} else {…}` — `SkeletonRender.lean:112-114`, `Skeleton.lean:299-305` | as `choose` | as `choose`: `plan` maps `.branch` to `.choose` after the value/tape agreement check — `Runs.lean:191-201` | **≠** — same row as `choose`; the value-agreement refusal (`refusedValue`, `Runs.lean:53-56`) has no `Prim` image at all. |
| `enter` / `region-enter` (checked) | `yield* regions.enter(1); const r1 = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {…}), (exit) => regions.leave(1, exit)))` — `SkeletonRender.lean:118-122`, `.lake/packages/typescript/TypeScript/Render.lean:206-210` | `Effect.scoped` = `WithFiber` + fresh `Scope` in the fiber context + `onExitPrimitive` — `effect.ts:3938-3947`; `Effect.onExit` = **`OnExit`** — `effect.ts:4002-4029` | `Prim.onSuccess (compiled body) (RegionName.regionCont …)` — `RegionSimulation.lean:335-339` | **≠, deliberately** — the compile emits `onSuccess`, not `onExit`, so that no `finalizer` row is manufactured (`RegionSimulation.lean:68-73`). `Prim` models no `Context`/`setContext`, so the `WithFiber` half is unmodelled (`docs/FRAMES-DAG.md:252`). |
| `acquire` / `region-acquire` (checked) | `const a1 = yield* Effect.acquireRelease(cell.acquire(x), (a, exit) => regions.finalizer(1, exit).pipe(Effect.andThen(cell.release(a))))` — `SkeletonRender.lean:128-134` | **no opcode of its own**: `contextWith` (=`WithFiber`) + `uninterruptibleMask` (pushes `SetInterruptible`) + `flatMap` (`OnSuccess`) + `scopeAddFinalizerExit` — `effect.ts:3971-3987`, `3847-3851`. The release is *registered in one `Scope`*, never a frame. | `Prim.onSuccess (sync) (cont)`, then in the table `Prim.onExit body (RegionName.fin region point) false` — `RegionSimulation.lean:344-345`, `383-385` | **≠ — the root of `E4-TARGET-CE-019`.** One `OnExit` per acquire nests, so `Exit.restoreAfterFinalizer` (`Exit.lean:54-68`) feeds a later release's failure into an earlier release's closing exit. rc.112 closes the single scope with `exitAsVoidAll`, no nesting, no merge into the exit each finalizer sees (`effect.ts:3826`, `2025-2038`). |
| `leave` / `region-leave` (checked) | `return b2p1` inside the nested generator — `SkeletonRender.lean:135`, `Skeleton.lean:341-344` | generator return → `OnExit`'s `[contA]` (`effect.ts:4020-4022`) → `Effect.scoped`'s own `OnExit` closes the scope | `Prim.success value` — `RegionSimulation.lean:347-349` | = |
| masked region / `region-masked` (pinned) | `Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(…), …)))` — `SkeletonRender.lean:123-127`, `Render.lean:211-215`; selected at `RegionLower.lean:105` | `uninterruptible` = `WithFiber` pushing `setInterruptibleTrue` — `effect.ts:4302-4310`, singleton at `4321`; the frame itself is `SetInterruptible` — `effect.ts:4312-4320` | none. `Prim.setInterruptible` exists (`Runtime.lean:120`) but no compile emits it; the mask is a `List RegionId` + `Bool` in the runner — `Effect4/Flow/Interrupt.lean:170-184` | **∅** — not modelled by any compile. |
| interrupt point / `interrupt-point` (pinned) | `yield* interrupts.point(1000001)` — `SkeletonRender.lean:115-116`, `Skeleton.lean:307-314` | delivery is `FiberImpl.interruptUnsafe`: `causeInterrupt(fiberId)`, stack annotation, accumulation by `causeCombine` — `effect.ts:574-595`, `140-145` | none. The fields exist (`interruptedCause`, `deferredInterrupt`, `Runtime.lean:228-231`) but nothing in `Runtime.lean` ever *writes* `interruptedCause` (`Runtime.lean:2216-2222`), so fence A proves the interrupt half inert on the fragment | **∅** — an interrupt-carrying compile needs a new Runtime entry point, not a compile arm. |
| service lookup / `service-acquire` (checked) | `const cell = yield* Cell` — `EffectV4.lean:338-340` | the `Context.Key` **is** the Effect: `export const service = (service) => service` — `effect.ts:2059` | none. `Prim.withFiber` (`Runtime.lean:103`) is the nearest and takes a thunk *name*; `Prim` carries no `Context` | **∅** — refused, not modelled (`docs/FRAMES-DAG.md:253`, TRACE-DAG separation 6, `docs/TRACE-DAG.md:88-94`). |
| pure atom / literal / `atom-call`, `flow-atom`, `flow-literal` (checked / covered) | `succ(x)`, `let a1 = 5` — `EffectV4.lean:342-344`, `SkeletonRender.lean:98-103`, `Skeleton.lean:271-281` | none — plain JS | the compile treats them as plan `.perform`s answered by the oracle (`RegionSimulation.lean:234-249`); the runner suppresses their rows via `service.pure` (`Region.lean:122-129`) | ∅ |
| aborting operation / `error-abort` (checked) | a *type*, `Effect.Effect<A, E>` — `EffectV4.lean:175-178` | `fail` = `exitFail` = `causeFail` + **`Failure`** — `core.ts:529-531, 550`; the failure loop skips `contE` frames while interrupted — `core.ts:539-546` | `Prim.failure (Cause.fail error)` — `RegionSimulation.lean:377`, `Runtime.lean:97` | = |
| structured form / `structured-loop`, `structured-merge`, `structured-continue`, `structured-break` (covered), `dispatch-fallback` (checked) | labelled `while (true)`, `label: {}`, `continue l`, `break l` — `SkeletonRender.lean:92-95`, `Skeleton.lean:346-360`; fallback `StructuredLower.lean:30-33` | none — plain JS control flow | none: the compile recurses | ∅ |
| **whole program** (every rule above sits inside it) | `export const p = (x: T) => Effect.gen(function* () { … })` — `Render.lean:249-251`; carries no rule tag | `gen` = `Suspend` wrapping `fromIteratorUnsafe` = **`Iterator`** — `effect.ts:1192-1196`, `1356-1379`; `yield*` protocol at `core.ts:103-105` | **none** — no compile in the repository emits `Prim.iterator` or `Prim.suspend` | **∅ / ≠** — the largest silent modelling decision: the compile replaces the generator with an explicit `onSuccess` chain. |

Three facts about this table that are worth stating on their own.

**`Effect.interruptible` is never emitted.** The brief's phrase
"`Effect.interruptible`/mask for interrupt points" does not match the lowering:
the string appears nowhere in `Effect4/`, `harness/` or the pinned `typescript`
package. Masking is one-sided — only `Effect.uninterruptible`
(`Render.lean:213`), reached solely by `region-masked` — and *interruptibility*
is not a combinator at all but a service call, `interrupts.point(<site>)`
(`SkeletonRender.lean:116`). There is likewise no
`Effect.uninterruptibleMask` and no bare `Effect.onExit`/`Effect.scoped`
outside the two `scopedGen*` spellings. So the mask half of rc.112's
`SetInterruptible` census row (`op.SetInterruptible`, green in
`docs/FRAMES-DAG.md`) has **no lowering to be faithful to**, which is a
smaller obligation than it looks.

**`Rule.all` has 29 entries and none of them is `proved-lean-side`.** The
length is pinned at `Effect4Test/Target/TypeScript/FlowLowerContract.lean:43`;
the ledger's counts are `checked 12`, `covered 12`, `pinned 5`, and the `proof`
column is `-` on all 29 rows (`generated/lowering-coverage.tsv`). A compile
packet would supply the ledger's first `proof` entries — which the vocabulary
allows independently of the host columns (`docs/LOWERING-COVERAGE.md:56`) and
which move no state by themselves.

**`error-abort` is the only rule that emits its own string** (`EffectV4.lean:179`);
every other rule builds a `Skeleton`, which `SkeletonRender.lean` turns into a
`TypeScript.Stmt`, which `.lake/packages/typescript/TypeScript/Render.lean`
spells. That three-stage path is why the (a) column carries two line numbers.

Verification labels for §1: the (a) column is **verified by reading** every cited
definition and its renderer. The (b) column is **verified by reading** the pinned
rc.112 sources at the cited lines (two exceptions under "What I could not verify").
The (c) column is **verified by reading** `compileRegion` and `regionInterp` in full.

Two counts worth stating together: rc.112 has 17 opcodes (three factories,
`core.ts:388, 418, 462`); `Prim` declares 14 and names the three it omits —
`Yield`, `Async`, `AsyncFinalizer` (`Runtime.lean:89-92`). The compile emits 5 of
the 14: `success`, `failure`, `sync`, `onSuccess`, `onExit`, plus `setInterruptible`
only as `Prim.ensure` pushes it (`Runtime.lean:560-565`).

## 2. The general compile, stated

### 2.1 Where to start from

Not from `Flow.denote`. The denotation is a `Program (FullSig a)`
(`Effect4/Semantics/Denotation.lean:63, 473`) or, with regions, a
`Program (ScopeSig ⊕ₛ (RegionOpSig ⊕ₛ DecSig))`
(`Effect4/Semantics/RegionDenotation.lean:150-151`), and `Program` has `pure` and
`vis` and no bracket former — the reason `FrameSimulation.lean:566-575` says the
finalizer half is not statable there. The scope summand's `leave` answers
`Option Failures` (`RegionDenotation.lean:133-137`) with the whole close hidden
inside `scopeHandler`'s arm (`:205-210`), so compiling from the denotation would
have to compile a handler, not a program.

Start from the **region runner's configuration**, which is what
`compileRegion` already does: `Config = ⟨fuel, block, env, tape⟩`
(`RegionSimulation.lean:145-154`), first-order, `DecidableEq`, and unique per run
because the runner spends one fuel unit per block (`:92-94`).

### 2.2 The compile, term by term (the four repairs marked ▲)

Write `compileFlow` for the repaired compile. Arms that stay as they are:

- `ret` → `Prim.success v` (`RegionSimulation.lean:323`).
- `jump` → recurse at `fuel-1` (`:324`).
- `choose`/`branch` → recurse on the tape-fixed edge (`:331`). Keep it compile-time:
  the compared mask discards `decide` rows (`:208-210`), and giving decisions a
  frame shadow would need a new `FrameEvent` constructor and a re-freeze of
  `test/contracts/frames.contract.md`.
- `perform` → `Prim.onSuccess (Prim.sync point) (RegionName.cont point)` (`:326`),
  with `contA` continuing at the plan's target (`:379-381`).
- `enter` → `Prim.onSuccess (compiled body) (RegionName.regionCont region point)`
  (`:335-339`); `leave` → `Prim.success v` (`:347-349`).

▲ **Repair 1 — `acquire` and the close.** Replace the per-acquire
`Prim.onExit body (RegionName.fin region point) false` (`:383-385`) with **one**
`Prim.onExit` per region, pushed at `enter`, whose finalizer name is
`RegionName.close region enterPoint`. Its `PrimInterp.finalizerExit`
(`Runtime.lean:201`) answers
`ScopeMachine.finish (releases.map (oracle.release ·))`, i.e.
`Exit.asVoidAll` of the release exits (`ScopeMachine.lean:70-73`,
`Exit.lean:71-76`) — the exact function rc.112 uses (`effect.ts:2025-2038`,
called from `scopeCloseFinalizers` at `:3826`) and the exact function
`closeFrame_failure_merge` relates the runner to (`Region.lean:446-453`). Then
every release sees the original closing exit, as `closeReleases` gives it
(`Region.lean:134-145`) and as `ScopeMachine.request_uses_original` states
(`ScopeMachine.lean:100-104`). The `Frame.toScope` bridge is already proved:
`Frame.toScope_closeOrder` (`Region.lean:86-92`) says the runner's `releases`
list *is* that scope's `closeOrder`.

One detail Repair 1 must not flatten: `Scope.closeResult` has **three** arms, not
two — at exactly one finalizer it returns that finalizer's own exit *unmerged*
(`Effect4/Runtime/Scope.lean:796-803`, `closeResult_single`), and
`E4-RUN-CE-009` (`REGISTER.md:181`) exists precisely to forbid always-merging.
`ScopeMachine.finish` already has the three arms (`ScopeMachine.lean:70-73`),
which is another reason to route through it rather than call `Exit.asVoidAll`
directly. And the merge is concatenation, not union:
`closeResultPinned [1,1] = failure [1,1]`
(`Effect4Test/Counterexamples/Runtime/Scope.lean:396`, `merge_is_concatenation_not_union`),
matching `Exit.asVoidAll_keeps_duplicates` and rc.112's own
`exitAsVoidAll` (`effect.ts:2025-2038`).

The cost: `finalizerExit` sees only the name and the closing exit, so
`RegionName.close` must determine the registration list. That is the
`leaveConfig` obligation the module header already names (`:122-128`) — a
function that walks a region body to its close under the oracle. It is
unavoidable in some form; making it a *hypothesis* (an oracle field
`registrations : Config → List Config` with a proof that it agrees with the
runner's `Frame.releases`) is smaller than a second copy of the runner and is
what §2.4's `hOracle` should carry.

▲ **Repair 2 — frontiers.** Eight arms currently send live work to
`Prim.failure Cause.empty` (`RegionSimulation.lean:314, 317, 332, 333, 334, 340,
346, 350`), and `Exit.toOutcome` of an empty cause is `.interrupted`
(`Simulation.lean:37-42`) — verified by the receipt
`source_fuel_zero_machine = some [.done .interrupted]`
(`Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean:77-78`).
Two acceptable shapes: `compileFlow : … → Option Code` with the theorem
conditioned on `some`, or a residual `Prim.suspend ⟨point⟩` whose `suspendBody`
is never demanded so the machine stays `FrameStep.running`. The second is
better: `FrameStep.running` at exhausted fuel is DB-04's live frontier by
construction (`Runtime.lean:277-279`).

▲ **Repair 3 — `performCatch`.** Emit
`Prim.onSuccessAndFailure (Prim.sync point) (RegionName.cont point) (RegionName.catch point)`
and let `syncValue` produce `Prim.failure (Cause.fail e)` on an `.error` answer,
so the machine's `armE` (`Runtime.lean:754-755`) resumes at the failure
successor. This matches `Effect.result` → `OnSuccessAndFailure`
(`effect.ts:3417-3420`) and removes the current sleight of hand where the error
is resolved inside `contA` (`RegionSimulation.lean:374-377`) and no frame ever
sees a `Cause`.

▲ **Repair 4 — interrupts, deferred.** `interruptPoint` cannot be compiled today:
`step` of a `setInterruptible` as the *current* effect is a defect by design
(`Runtime.lean:1706-1708`, `step_setInterruptible_not_evaluable` at `:1964`), so
masks are installed by `FrameFiber.uninterruptible` / `interruptibleRegion`
(`:2045-2071`), which are fiber operations, not program syntax; and *delivery*
needs something to write `interruptedCause`, which nothing in `Runtime.lean`
does (`:2216-2222`). The compile packet should carry `masked = []`, `itape = []`
as a named hypothesis and leave `Effect4/Flow/Interrupt.lean` alone.

**Loops.** `jump` cycles are handled by unrolling: `compileRegion` recurses on
`fuel`, so a cyclic flow compiles to a finite `Prim` whose size is bounded by the
runner's fuel, which is why `regionBound runnerFuel = 4 * runnerFuel + 1`
(`RegionSimulation.lean:437`). Keep it. `Prim.whileLoop`'s cursor is one `β`
(`Runtime.lean:122`, `PrimInterp.loopTest/loopBody/loopStep` at `:207-211`) and a
flow's environment is a `List Val`, so a `whileLoop` compile would need a
`Val`-encoding of the environment and would buy nothing: the tape already bounds
the run (`Approximation.lean:2139`, `runRegions_fuelFor_finishes` at `:2182`).

### 2.3 The theorem statements

Both statements below were written into a scratch file and **elaborated**
against the built library with `sorry` proofs — no type errors, only the two
expected `declaration uses 'sorry'` warnings. So the shapes are known to
typecheck; nothing about their truth is claimed.

**T5 (trace equation).** The docstring's `regions_simulate`
(`RegionSimulation.lean:109-121`), spelled as Lean:

```lean
theorem regions_simulate {Ty : Type} [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (flow : CheckedRegionFlow alphabet)
    (answerOf : alphabet.Op → Val → Except Val Val)
    (service : Effect4.Flow.RegionService alphabet Id)
    (nameOf : alphabet.Op → String)
    (tape : Effect4.Flow.Tape) (input : Val) (fuel' fuel : Nat)
    (hOracle : ∀ op request, service.handle op request = answerOf op request)
    (hfuel : Effect4.RegionSimulation.regionBound fuel' ≤ fuel) :
    Effect4.RegionSimulation.traceOfRun
        (Effect4.FrameFiber.run
          (Effect4.RegionSimulation.regionInterp alphabet flow.flow
            (Effect4.RegionSimulation.statelessOracle alphabet flow.flow answerOf))
          fuel
          (Effect4.FrameFiber.start
            (Effect4.RegionSimulation.compileAt alphabet flow.flow
              ⟨fuel', flow.flow.entry, [input], tape⟩))).2
      = Effects.Trace.project Effect4.RegionSimulation.finalizerAndOutcomeMask
          (((Effect4.Flow.runRegions fuel' flow service nameOf tape input).run []).2)
```

`hOracle` in this form is the `stateless` hypothesis of
`closeFrame_failure_closeResult` (`Region.lean:463-466`) at `M := Id`. For a
stateful service it becomes `∀ op request s, service.handle op request s =
(answerOf op request, s)` and the theorem is stated over `StateT σ Id`.

**T6 (exit equation).** The prose statement carries only the trace; the exit is
the half that actually distinguishes the models, and it needs the merged failure
list, so it is stated against `runRegionsCause` (`Region.lean:254`) rather than
`runRegions`:

```lean
theorem regions_simulate_exit … :
    (Effect4.FrameFiber.run (regionInterp …) fuel
        (Effect4.FrameFiber.start (compileAt …))).1
      = Effect4.FrameStep.finished
          (match ((Effect4.Flow.runRegionsCause fuel' flow service nameOf tape input).run []).1 with
            | ((.done value, _), _) => Effect4.Exit.success value
            | ((_, _), failures) => Effect4.Exit.failure
                (Effect4.RegionSimulation.causeOfFailures failures))
```

`causeOfFailures` / `failuresOfCause` are the section and retraction already
proved (`RegionSimulation.lean:448-467`), and `toOutcome_combine` (`:496-505`)
is why T5 is insensitive to whichever merge the compile uses while T6 is not.

**T7 (finalizer order).** Already proved in general, and needs no repair beyond
Repair 1's hypothesis change: `unwind_failure` (`:855-865`) says a failing exit
runs exactly the finalizers a fragment stack names, in pop order, *every one
against the same exit*, and `close_success` (`:964-976`) says the same for a
closing value. Their `hfin` premise (`∀ name exit, finalizerExit name exit =
Exit.success ()`, `:856`) is *exactly* the "no release fails" restriction that
`E4-TARGET-CE-019` attacks; after Repair 1 the premise is needed only for the
region's single close-finalizer, whose exit is `asVoidAll` of the releases and
therefore already carries every failure — the theorem generalises rather than
being reproved.

**T8 (endpoint classification).** The register's actual demand
(`E4-TARGET-CE-020`/`-021`): a relation, at every prefix, matching continuation,
environment, tape, open registrations, service state, closing state, and
distinguishing live suspension from refusal from completion. The runner's four
endpoints are `RunResult.done`/`failed`/`frontier`/`refusedSite`/`refusedValue`
(`Runs.lean:43-57`); `refusedSite`/`refusedValue` have no `Exit` image at all, so
T8 cannot be an equation between exits and must be a three-way classifier.
`ScopeMachine.runState_prefix` (`ScopeMachine.lean:322-339`) is the template:
partition plus service-state receipt at every pause.

### 2.4 What `PrimInterp`'s pure-total shape forces

`PrimInterp` is a record of eleven pure total functions plus a defect payload
(`Runtime.lean:191-215`). There is no monad and no state parameter, and
`FrameSimulation.lean:23-30` already records that the answers are supplied, not
computed.

Is the answer tape still an adequate oracle with regions and catches? **Yes for a
stateless service, no in general, and no state slot is needed either way.**

- Adequate, because a *point-keyed* oracle beats an occurrence-indexed one:
  `Config` carries the runner's fuel, so a configuration is reached at most once
  in a run (`RegionSimulation.lean:92-94`) and one function `Config → Except Val
  Val` names every answer. `RegionOracle` already has the second field a region
  needs — `release : Config → Except Val Val` (`:222-226`) — so a catch adds no
  field (Repair 3 reads the same `answer`) and Repair 1 adds one more,
  `registrations : Config → List Config`.
- Inadequate for a stateful service *at the finalizer*, and only there.
  `finalizerExit : ν → Exit β ε δ ι α → Exit Unit ε δ ι α` (`:201`) sees the
  name and the closing exit and nothing else, so it cannot depend on state a
  release wrote after registration. The runner can (`closeReleases` threads
  `RunM M`, `Region.lean:134-145`). That is the gap, and it is the same one D2
  already fenced with `stateless` (`Region.lean:465`) and
  `statelessOracle` (`RegionSimulation.lean:419-431`).
- Do **not** add a state slot. `PrimInterp` carrying `σ` would change `Prim`'s
  parameterisation, and the whole frame census
  (`generated/effect-runtime-census.tsv`, 28 green-able rows per
  `docs/FRAMES-DAG.md:264`) is stated over the current shape and frozen by
  `test/contracts/frames.contract.md`. Carry `stateless` as a named hypothesis,
  which is what the existing D2 lemma does and what the theorem above spells.

## 3. The refutations, understood

| Row | Exactly what is refuted | Witness | Restriction that makes it true | Recommendation | Cost |
| --- | --- | --- | --- | --- | --- |
| `E4-TARGET-CE-019` (`REGISTER.md:136`) | "Registrations sharing one scope can compile to independent nested `onExit` frames even when a release fails." Concretely: runner writes `[finalizer 1 (success 5), finalizer 1 (success 5), done (failure "boom")]`; machine writes `[finalizer 1 (success 5), finalizer 1 (failure "boom"), done (failure "boom")]` | `RegionSimulationBoundary.lean:43-52`; positive control at `:64-69`; `unrestricted_finite_agreement_false` at `:141-143` | `hfin`: no release fails (`RegionSimulation.lean:856`) | **(ii) change the model — the compile, not the runner.** rc.112 closes one scope with `exitAsVoidAll` (`effect.ts:3826, 2025-2038`), which is what `closeReleases` does (`Region.lean:134-145`) and what `ScopeMachine.request_uses_original` (`:100`) states. The nested-`onExit` compile is the only party that disagrees with rc.112. | `compileRegion`'s acquire arm + `regionInterp.contA`'s `some region` case (`RegionSimulation.lean:344, 383-385`); the three evaluated instances in `Effect4Test/Semantics/RegionSimulationContract.lean`; `RegionSimulationBoundary.lean:47-52` inverts from a divergence to an agreement. **No golden moves**: a fallible release has no lowering (`E4-TARGET-CE-012`, `REGISTER.md:129`), so the host never saw this. Census: none. TRACE-DAG: `frame-simulation` (`docs/TRACE-DAG.md:50`). |
| `E4-TARGET-CE-020` (`:137`) | "Compiling exhausted source fuel to an empty failure preserves a live region run after frontier rows are masked out." Runner at fuel 0 → `frontier (fuel 0)`, projected log `[]`; machine → `[done interrupted]`, and after an acquire also `[finalizer 1 interrupted, done interrupted]` | `RegionSimulationBoundary.lean:72-93` | `regionFuelFor flow tape ≤ fuel'` (`Approximation.lean:2139`, `runRegions_fuelFor_finishes` at `:2182`) | **(ii) change the model, and (iii) say the restriction in the settled theorem.** A live frontier is never a result (DB-04, `Runtime.lean:277-279`); a compile that finalises one is wrong independently of any hypothesis. Repair 2, then state T5/T6 at sufficient fuel and T8 for the prefix. | The seven `Prim.failure Cause.empty` arms (`RegionSimulation.lean:314, 317, 332-334, 340, 346, 350`); `RegionSimulationBoundary.lean:75-93` becomes a statement about `FrameStep.running`. No goldens, no ledger rows, no census rows. |
| `E4-TARGET-CE-021` (`:138`) | "An unanswered region decision may become an empty failure without changing finalizer/outcome observations." A resource-bearing admitted cycle waits at site 7 while the compiled frames finalise and report interruption | `RegionSimulationBoundary.lean:96-122`; false-decision control at `:128-133`; mismatch stays a refusal at `:124-126` | complete compatible tape, plus Repair 2 | **(ii) + (iii).** Same repair as `-020` for the finalisation half; the classification half is genuinely new work — `refusedSite`/`refusedValue` (`Runs.lean:52-56`) have no `Exit` and no `Prim` image, so T8 must classify three endpoints rather than equate two exits. | Same file; plus a new `Frontier`/refusal carrier on the compile's residual. Touches `docs/TRACE-DAG.md:50`'s "endpoint classification" clause verbatim. |
| `E4-FLOW-CE-019` (`:35`) | "A release that fails while a region closes with a failure replaces the failure" | `Effect4Test/Flow/RegionRunnerContract.lean`, `releaseFails`/`nested`; host `regionNested.empty`, `regionTwoFail.empty` under `m1` | — | **(i) already done, keep and re-read as historical.** The row's "Forced repair" column ("the runner keeps the first failure") is superseded: D2 gave `closeFrame` the merged list (`Region.lean:446-453`) and `runRegions` projects the first (`Region.lean:262-266`). `FrameSimulation.lean:576-582` records the ruling. The plan's §1 bullet and §6 D4 remainder (`docs/research/2026-09-03-reification-plan.md:27-30, 248`) are stale on this point. | Documentation only: amend the register row's repair column to point at `E4-FLOW-CE-021`'s. |
| `E4-FLOW-CE-020` (`:36`) | "Releases may run in registration order or with their own region's exit" | `RegionRunnerContract.lean`; host `regionTwoFail.empty` under `m2` | — | **(i)/(ii): the runner is already right; the compile breaks the *exit* half while preserving the *order* half.** Repair 1 fixes it; `Frame.toScope_closeOrder` (`Region.lean:86-92`) and `unwindNames`/`closeNames` (`RegionSimulation.lean:555-583`) already carry the order half. | Subsumed by Repair 1. |
| `E4-FLOW-CE-021` (`:37`) | "A close that merges several failures reports only the first and forgets the rest" | `closeFrame_failure_merge` (`Region.lean:446`); `ApproximationContract.lean` pins `[boom, boom]` with wire `failed boom` | wire projection only | **(iii) keep the restriction and say so.** `toOutcome_combine` (`RegionSimulation.lean:496-505`) proves the merge is invisible to the wire with **no** annotation hypothesis; §5(b) of `2026-09-03-frame-simulation.md:288-301` stays live only for whole-cause statements. Sharp rc.112 fact to record: `causeCombine` dedups by structural equality *including annotations*, and `Interrupt` compares annotation maps by reference (`effect.ts:242-258, 125-131`; `core.ts:214` builds a fresh `Map` per annotation), while `exitAsVoidAll` does not dedup at all (`effect.ts:2025-2038`). So `Cause.combine` is the wrong merge for a scope close and `Exit.asVoidAll` is the right one — a second, independent argument for Repair 1, and it is already decided in the kernel: `merge_is_concatenation_not_union` (`Effect4Test/Counterexamples/Runtime/Scope.lean:396`) and `E4-SEM-CE-006`'s `join_is_not_combine` (`Effect4Test/Counterexamples/Semantics/CauseExit.lean:293`). | None; the row stands. Add the rc.112 dedup asymmetry as a note on the row. |
| `E4-FLOW-CE-023` (`:39`) — **the interrupt-identity row** | "`Outcome.interrupted` carries no payload, so an interrupted close may hand its releases the exit the body would have had, or the failure arm" | `Effect4Test/Counterexamples/Flow/Interrupt.lean:133-146`; the identity receipt at `:150-151`: `frameExit .interrupted = Exit.failure ⟨[.interrupt none ReasonAnnotations.empty]⟩` | — | **(iii) keep, and record the asymmetry.** The runner's interrupt cause carries **no interruptor** (`Region.lean:104-108`), while rc.112 stamps `fiberId` plus stack annotations at `effect.ts:574-595` and `Effect4`'s own `Cause.interrupt (some 1)` *can* carry one (`Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean:134-139`, `interruptors_accumulate`). So the identity is representable in the cause carrier and simply absent from the Flow face — exactly what `docs/TRACE-DAG.md:62` lists as open. | None for a compile packet; it is packet P6's first obligation and A1's alphabet is its prerequisite. |
| `E4-TARGET-CE-012` (`:129`) | "a fallible release [may lower] to `Effect.acquireRelease`" | `RegionLowerContract.lean`, `fallibleRelease`: `Region.lowerDispatch` returns `none`; guard at `RegionLower.lean:117-119` | — | **(iii) keep.** It is why `E4-TARGET-CE-019` has no host golden and why `hfin` looked free. State in the packet that Repair 1's benefit is Lean-only and the host stays silent. | None. |
| `E4-RUN-CE-025` (`:194`) | "Restoring interruptibility replaces any completed scope exit with its pending interruption, including an existing cleanup failure" | `Effect4Test/Counterexamples/Runtime/ScopeRestorationBoundary.lean`; host `harness/trace/scope-restoration.mjs` | — | **(i) already repaired; reuse.** `ScopeRestoration.resumeClosedScope_failure_pending` (`:63-78`) is the repaired law and is exactly the arm an interrupt-carrying compile needs at a region close. | None now; it is a prerequisite for packet P6. |

The three `E4-TARGET-CE-019/020/021` rows have **one** structural cause between
them and **one** hypothesis (`hfin`, sufficient fuel, complete tape) each. Only
`-019`'s is dishonest for a reification claim, because the host cannot see the
case it excludes.

## 4. What `ScopeMachine` and `ScopeRestoration` already prove

### `Effect4/Runtime/ScopeMachine.lean` (341 lines)

Carrier `State κ φ β ε δ ι α` (`:36-42`): the retained `Scope`, the **fixed**
`original` closing exit, `pending` (the remaining close order), `captured` (the
ordered journal of operation/reply pairs), and a three-value `Phase` (`:29-33`).

Steps: `start` (`:46`) closes the scope *before* any request; `advance` (`:49`)
exposes one pending request or completes; `request?` (`:56`) returns
`(ordinal, operation, original)`; `respond` (`:64`) accepts only the current
ordinal; `runState` (`:89`) is the explicit-state interpreter, answering one
request per step. `bound scope = 2 * closeOrder.length + 1` (`:87`) — note this
is `FrameSimulation.bound`'s shape (`FrameSimulation.lean:175`), independent of
source fuel.

Main theorems: `request_uses_original` (`:100-104`), `respond_rejects_wrong_id`
(`:107`), `respond_rejects_wrong_phase` (`:114`), `runState_zero` (`:123`),
`runState_add` (`:131`), `runState_scope` (`:146`), `runState_complete` (`:191`)
= `Scope.closeExitsM`, `runState_restore` (`:217`) = the exact restoration
policy, `runState_result` (`:233`) = `Scope.closeResult` for a pure callback,
and `runState_prefix` (`:322`) — the partition of `closeOrder` into
captured/waiting/pending plus a service-state receipt, at **every** pause.

### `Effect4/Runtime/ScopeRestoration.lean` (181 lines)

Carrier: none of its own. `resumeClosedScope` (`:35-39`) maps a *completed*
`ScopeMachine.restore?` exit through `FrameFiber.step`. Nine laws:
`_unfinished` (`:42`), `_success_pending` (`:51`), `_failure_pending` (`:63`),
`_complete` (`:81`), `_success_no_pending` (`:102`), `_already_masked` (`:123`),
`_masked_continuation` (`:133`), `_failure_cleanup` (`:149`),
`_success_cleanup_failure` (`:163`).

### Reuse, subsume, or leave

**Reuse, as the region half of the compile.** Concretely, Repair 1's
`finalizerExit (RegionName.close region point)` should be
`ScopeMachine.result?` of the completed close of `Frame.toScope`
(`Region.lean:79-83`), and `resumeClosedScope_complete` (`:81-99`) is then
literally the step law for a region close: it already equates "run the machine
to completion, restore, step the fiber" with "`closeExitsM`, restore, step".
`runState_prefix` is the template for T8. Neither module should be subsumed: they
are stated over an arbitrary `Scope` and an arbitrary `φ`, so they are reusable
by the interrupt packet and the layer packet as they stand.

**Which theorems are census clauses in disguise.** Not the two the question
guesses. The tags on the declarations say:

- `scope.close-state-first` → `runState_scope` (`ScopeMachine.lean:145`).
- `scope.close-sequential` → `request_uses_original` (`:99`) and
  `resumeClosedScope_complete` (`ScopeRestoration.lean:80`).
- `scope.close-merge` → `runState_restore` (`:216`) and `runState_result` (`:232`).
- `cause.finalizer-merge` → `resumeClosedScope_failure_cleanup`
  (`ScopeRestoration.lean:148`).
- `scope.acquire-release` → exactly one: `resumeClosedScope_already_masked`
  (`:122`), the "an uninterruptible region inside one adds no second restoring
  frame" clause, i.e. `FrameFiber.uninterruptible_already_masked`
  (`Runtime.lean:2083`) at a composite.
- `scope.scoped` has **no** ScopeMachine/ScopeRestoration witness. Its frame-side
  clause is `Prim.scopedFrame`/`scopedFrame_eq`/`scopedFrame_finalizer_masked`/
  `step_scopedFrame` (`Runtime.lean:2156, 2161, 2166, 2200`), and its scope-side
  clause is `Scope.runScoped_*` (`docs/SCOPE-DAG.md:146`).

Both `scope.scoped` and `scope.acquire-release` stay **partial** whatever the
compile does, and the reason is named in two places: the missing clauses are
"installs a fresh scope in the fiber context", "restoring the previous context
first" and "with the captured context" — a fiber `Context` and `setContext`,
which `Prim` does not model (`docs/FRAMES-DAG.md:252-253`,
`docs/SCOPE-DAG.md:146-147`). rc.112 confirms the shape: `scoped` is
`withFiber` + `setContext` + `onExitPrimitive` (`effect.ts:3938-3947`) and
context provision is itself `withFiber` + `onExitPrimitive`
(`effect.ts:2073, 2087-2096`). **No compile packet should be sold as turning
either row green.**

## 5. The skeleton and structured forms

### Does T4 still need its own denotation?

**Yes, and it should keep it.** T4 today is
`skeletonStructured_denote_dispatch_of_emitted`
(`Effect4/Target/TypeScript/StructureSemantics.lean:1219-1231`): an equation
between two `Skeleton.denote` **Programs**, derived from
`skeletonStructured_denote_of_fuelFor_le` (`:1167`) and
`skeletonDispatch_denote` (`SkeletonSemantics.lean:2321`) both against
`Flow.denote`. `docs/TRACE-DAG.md:60` records that it is an instance of
`Flow.Equiv`.

Compiling both skeleton forms to `Prim` and comparing there would be strictly
weaker, for two reasons:

1. A compile is a function of the denotation, so equal `Program`s give equal
   `Prim`s automatically; the `Prim` statement is a corollary of T4, never a
   replacement.
2. The converse fails: two compiled programs can run identically under **one**
   oracle and denote differently, because the oracle is what supplies every
   answer (`FrameSimulation.lean:23-30`). A `Prim` comparison therefore has to
   carry `hOracle`, a hypothesis T4 does not need and whose universal
   quantification over tapes is exactly what `Flow.Equiv` already gives
   (`Effect4/Semantics/Equivalence.lean`, `docs/TRACE-DAG.md:60`).

The right statement is a congruence: `Flow.Equiv f g → compileAt f = compileAt g`
at every configuration, ~40 lines, worth having and worth nothing more.

### What `docs/TRACE-DAG.md` says each edge requires, and what a general compile closes

| Edge | Line | What it requires | Does a general compile close it? |
| --- | --- | --- | --- |
| `frame-simulation` | `:50` | replacement compiler; general finite-prefix relation matching continuation, environment, tape, open registrations, service state, closing state and endpoint classification; not "a second source run hidden in an oracle" | **The settled half, yes** (T5/T6/T7). The finite-prefix half needs T8, which is packet P5. The row also demands the current compiler's two named defects be gone — Repairs 1 and 2. |
| `semantics` | `:51` | runner = `interpret ∘ denote`, both halves | Already closed for the Lean pair (D1/D2). A compile adds the frame face; the host half stays evidence. |
| `bridges` | `:55` | a theorem relating a host row to a `FrameEvent` | **No, by construction** — `FRAME-L9-HOST-EVIDENCE` and the plan's refusal row. The compile gives `FrameEvent.toTrace`/`traceOf` (`Simulation.lean:46, 61`) a second consumer and nothing more. |
| `structured-agreement` | `:65` | ordinary Flow `Program` equality with interrupts disabled — closed; still open: region nodes, interrupt-point denotation, smaller target fuel, rendering, host | **No.** The open items are `Skeleton.denote` arms for `enterScoped`/`acquire`/`leave`/`interruptPoint`, i.e. a D3 packet on the skeleton side, not a compile packet. |
| `interrupts` | `:62` | the Flow result carries no full `Cause`/interrupt identity; `interruptPoint` in the skeleton denotation | **No** — Repair 4 defers it, and closing it needs a Runtime entry point plus A1's alphabet. |
| `coverage` | `:61` | 29 ledger rows (`checked 12`, `covered 12`, `pinned 5`), states in `generated/lowering-coverage.tsv` | **No state moves.** A compile packet can supply the ledger's *first* `proof` entries — today the `proof` column is `-` on all 29 rows — and `proved-lean-side` is independent of the host columns (`docs/LOWERING-COVERAGE.md:56`), so it adds a column, not a promotion. |

## 6. Obstacles and size

Ordered by severity. "Acceptable" means: acceptable as a named hypothesis in a
theorem that is offered as evidence for reification.

| # | Obstacle | Smallest neutralising hypothesis | Acceptable? |
| --- | --- | --- | --- |
| 1 | **Scope/frame structure mismatch**: one `onExit` per acquire instead of one `Scope` per region (`RegionSimulation.lean:383-385` vs `effect.ts:3971-3987, 3826`) | `hfin`: no release fails (`:856`) | **No.** `E4-TARGET-CE-012` means the excluded case has no host lowering, so the restriction hides the one place the two models differ while looking free. Repair, do not restrict. |
| 2 | **Frontier finalisation**: eight arms send live work to `Prim.failure Cause.empty` | `regionFuelFor flow tape ≤ fuel'` and a complete compatible tape | **For the settled theorem only.** Unacceptable as the general relation — that is precisely what `E4-TARGET-CE-020`/`-021`'s repair columns demand. |
| 3 | **`performCatch` shape**: `onSuccess` + `contA` instead of `onSuccessAndFailure` | none needed; the current shape is *not* unsound, only unfaithful | **No** — it is a faithfulness gap, not a proof gap; repair it while the file is open. |
| 4 | **`Cause.combine` dedup of annotated reasons** (`Cause.lean:687, 789`; rc.112 `effect.ts:242-258`, reference-equality on `Interrupt` annotations at `:125-131`) | `α := Unit` with empty annotations (`2026-09-03-frame-simulation.md:288-301`) | **Unnecessary** for wire statements (`toOutcome_combine`, `RegionSimulation.lean:496`) and **avoidable** for exit statements once Repair 1 uses `Exit.asVoidAll` (`Exit.lean:71-76`), which does not dedup — matching rc.112's own close path. |
| 5 | **`PrimInterp` purity** (`Runtime.lean:191-215`) | `stateless` (`Region.lean:465`), in oracle form `statelessOracle` (`RegionSimulation.lean:419`) | **Yes.** D2's L2 already carries it; it is stated, not hidden. Adding a state slot would re-freeze `test/contracts/frames.contract.md` and restate 28 census rows. |
| 6 | **Fuel/bound as a function of the tape** | `regionBound r = 4r + 1` (`:437`) over `regionFuelFor flow tape = (tape.length+1)*blocks.length+1` (`Approximation.lean:2139`, `Runs.lean:256`), with `run_add`/`run_mono` (`Runtime.lean:2487, 2539`) | **Yes**, and Repair 1 *lowers* the constant (one `onExit` push per region, not per acquire). Re-derive it in the packet. |
| 7 | **The `iterator` / `Effect.gen` gap**: every lowered program is `Effect.gen` → `Suspend` + `Iterator` (`effect.ts:1192-1196, 1356-1379`); no compile emits `Prim.iterator` | that the `Iterator` frame is observationally transparent for a generator that only `yield*`s Effects | **Only as a declared refusal.** `iterator_folds_inline` (`Runtime.lean:1091`) covers the inline fold, not the general case. Write a refusal row; do not leave it silent, and do not claim the compile emits "what the lowering emits". |
| 8 | **Service lookup**: `yield* Cell` is a `Context.Key` used as an Effect (`effect.ts:2059`); `Prim` has no `Context` | services are provided before the compared window (TRACE-DAG separation 6, `docs/TRACE-DAG.md:88-94`) | **Yes** — it is already the trace lane's standing rule and `docs/FRAMES-DAG.md:252-253` names it as the reason two census rows are partial. |
| 9 | **Interrupt identity across the wire**: nothing writes `interruptedCause` (`Runtime.lean:2216-2222`); `InterruptResult` carries no `Cause` (`Interrupt.lean:159-166`); rc.112 stamps `fiberId` and stack annotations at `effect.ts:574-595` | `masked = []`, `itape = []` | **Yes, for the compile packet.** Closing it is a Runtime packet mirroring `interruptUnsafe`, plus A1. |

### Size estimates

Lines of Lean, excluding batteries and axiom reports (add ~25 % for those). Basis:
`RegionSimulation.lean` is 1 068 lines for the current compile plus two general
theorems; `FrameSimulation.lean` is 593 for the straight-line half;
`ScopeMachine.lean` is 341 for a complete residual machine with ten laws.

## Recommended packet shape

Ordered. Each names its statement, its file fence, its size, its prerequisites,
the TRACE-DAG edges it touches and the census rows it touches (in every case:
none turns green).

**P1 — one scope per region in the compile (~350).**
*Statement:* `compileFlow`'s `enter` arm pushes one `Prim.onExit` per region whose
finalizer name is `RegionName.close region enterPoint`;
`regionInterp.finalizerExit` on that name is `ScopeMachine.finish` of the
oracle's release exits; `close_success`/`unwind_failure` re-proved with the
per-region premise. *Fence:* `Effect4/Semantics/RegionSimulation.lean`, plus the
three receipts in `Effect4Test/Semantics/RegionSimulationContract.lean` and
`Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean:43-69`.
*Prerequisites:* none. *Edges:* `frame-simulation`. *Rows:* closes
`E4-TARGET-CE-019`; re-reads `E4-FLOW-CE-020`. *Census:* none.

**P2 — frontier-preserving compile (~250).**
*Statement:* `compileFlow` never sends a frontier, stuck block, exhausted or
mismatched tape to an exit; the residual is `Prim.suspend ⟨point⟩` and the
machine stays `FrameStep.running`. *Fence:* same file; the eight arms at
`RegionSimulation.lean:314, 317, 332-334, 340, 346, 350`, and
`RegionSimulationBoundary.lean:72-133`. *Prerequisites:* P1 (same file).
*Edges:* `frame-simulation`, `approximation`. *Rows:* the finalisation half of
`E4-TARGET-CE-020`/`-021`. *Census:* none.

**P3 — `performCatch` as `onSuccessAndFailure` (~200).**
*Statement:* the caught failure is a real `Cause` on the machine side and the
`contE` arm resumes at the failure successor, matching `Effect.result` →
`OnSuccessAndFailure`. *Fence:* same file, plus a new receipt on the `jobRunner`
retry/requeue shapes. *Prerequisites:* P1. *Edges:* `frame-simulation`. *Rows:*
none; ledger row `perform-catch` (pinned) gains a `proof` entry at most.
*Census:* none — `op.OnSuccessAndFailure` is already green (`FRAMES-DAG.md`).

**P4 — the settled general theorem (~600, the workhorse).**
*Statement:* T5 and T6 of §2.3, verbatim (both elaborate today), with T7
generalised. Needs the `registrations`/`leaveConfig` oracle field and its
agreement lemma against `Frame.releases`. *Fence:* `RegionSimulation.lean`,
`Effect4Test/Semantics/RegionSimulationContract.lean`,
`test/contracts/frame-simulation.contract.md` (amend fence C).
*Prerequisites:* P1, P2, P3; reuses `runRegions_fuelFor_finishes`
(`Approximation.lean:2182`), `run_add`/`run_mono` (`Runtime.lean:2487, 2539`),
`Frame.toScope_closeOrder` (`Region.lean:86`). *Edges:* closes the settled half
of `frame-simulation`; gives `bridges` a second Lean-side consumer without
closing it. *Census:* none.

**P5 — the finite-prefix / residual-state relation (~500).**
*Statement:* T8 — a relation matching continuation, environment, tape, open
registrations, service state, closing state and endpoint classification at every
prefix, distinguishing live suspension, refusal and completion. *Fence:* a new
module (`Effect4/Semantics/RegionPrefix.lean`) plus the register rows.
*Prerequisites:* P2, P4; template is `ScopeMachine.runState_prefix` (`:322`).
*Edges:* closes the remaining clause of `frame-simulation` as that row words it.
*Rows:* closes the classification half of `E4-TARGET-CE-020`/`-021`. *Census:*
none.

**P6 — the interrupt half (~450 Lean + ~150 in a separate Runtime fence).**
*Statement:* a `FrameFiber.interruptUnsafe` mirroring `effect.ts:574-595` that
writes `interruptedCause` (breaking fence A's invariant, which must therefore be
restated as a fragment fact — it already is, `Runtime.lean:2213-2235`); the
compile emits `setInterruptible` frames for a masked region and the interrupt
runner's `interruptPoint` (`Interrupt.lean:178-184`) is simulated. *Fence:*
`Effect4/Runtime/Runtime.lean` (breaker: `test/contracts/frames.contract.md`),
then `RegionSimulation.lean`. *Prerequisites:* P4; A1's `Outcome.defect` and
interrupt producer; `ScopeRestoration`'s nine laws are the close-side arms and
`E4-RUN-CE-025` and `E4-RUN-CE-026` (`REGISTER.md:194-195`) are the pinned
repairs — the second one, "start the actual outer ScopeMachine with the inner
frame step's outgoing full Exit and service state", is the nesting rule this
packet has to obey. *Edges:* `interrupts`. *Rows:* the interruptor identity of
`E4-FLOW-CE-023` needs the Flow face to carry a `Cause`, which is the row's own
open item. *Census:* `op.SetInterruptible` and `checkpoint.*` are already green;
nothing moves.

Total ≈ 2 350 Lean lines across six packets, of which P1–P3 (~800) are repairs
to an existing file and P4–P6 (~1 550) are new theorems. P1 and P2 are worth
doing on their own merits even if nothing after them lands: they remove two
recorded model defects and cost nothing on the host.

## What I could not verify

- **rc.112 `Context.ts` and `Result.ts` are not in the vendored tree.**
  `internal/effect.ts` imports them at `:5` and `:29`, but `vendor/effect-4.0.0-rc.112/src/`
  contains only `Array.ts`, `Cause.ts`, `Deferred.ts`, `Exit.ts`, `Layer.ts`,
  `MutableRef.ts`, `Ref.ts`, `Scheduler.ts`, `SchemaRepresentation.ts`, `Scope.ts`
  and `internal/`. So the `Context.Key`'s own `[evaluate]` (the service-lookup
  row of §1) and `Result.succeed`/`Result.fail` (the `performCatch` row) cannot be
  cited by line. What *is* confirmed: neither is built by
  `makePrimitive`/`makePrimitiveProto` — those appear nowhere outside `core.ts`
  and `effect.ts`.
- **`andThen` and `loop` have no definition in `internal/effect.ts`** in this
  build. The `Effect.andThen` in the emitted release lambda
  (`SkeletonRender.lean:133`) must resolve to `flatMap` (`OnSuccess`) via the
  public `Effect.ts`, which is not vendored. Inferred, not verified.
- **No battery, gate or host script was run.** The only Lean executed was a
  scratch statement-shape probe (two `sorry`-ed theorems and four `example`s),
  which elaborated cleanly. `lake build` was not run, per the brief. So every
  claim about existing theorems is "this is what the source says", not "this
  compiles today" — although the library is built, so it does.
- **The size estimates are estimates**, calibrated against the three modules
  named in §6 and not against any attempt.
- **`Effect4/Target/TypeScript/SkeletonSemantics.lean` (2 489 lines) and
  `StructureSemantics.lean` (1 231) were read only at their theorem statements**
  (`:2321, :2374, :2444` and `:1167, :1219`). §5's claim that a `Prim` comparison
  would be weaker rests on the shape of those statements and on `Flow.Equiv`
  (`docs/TRACE-DAG.md:60`), not on their proofs.
- **`generated/lowering-coverage.tsv`'s agreement with the `lowering: rule.<id>`
  tag set** is checked by `scripts/check-lowering-coverage.sh`, which was not run.
  I located a tag for 28 of the 29 rules by grep and found `perform-tuple`'s at
  `SkeletonRender.lean:57` rather than in `Skeleton.lean`; that is consistent,
  not a drift.
- **Three premises in the brief are stale.** (1)
  `Effect4/Semantics/FrameSimulation.lean` is not the whole compile —
  `RegionSimulation.lean` (1 068 lines) is. (2) "the cause-merge divergence
  (`closeFrame` keeps the first failure)" was repaired by packet D2
  (`Region.lean:446-453`, `closeReleases` at `:134-145`; the ruling is recorded
  at `FrameSimulation.lean:576-582` and `COORDINATION.md:925-939`); the original
  finding is at `docs/research/2026-09-03-algebra-denotation.md:335-353` and
  `COORDINATION.md:786-790`, and
  `docs/research/2026-09-03-reification-plan.md:27-30, 248` still carries the old
  wording. (3) "`Effect.interruptible`/mask for interrupt points" — that
  combinator is never emitted; see §1.
- **Documentation drift observed, not fixed.** `docs/LOWERING-COVERAGE.md:31-36`
  still describes the census as eight straight-line rules with `choose`,
  `jump-dispatch`, `loop-labelled`, `merge-block`, `region-onExit`,
  `region-scoped` as "later" — six ids that do not exist in `Rule.id`; and
  `:121, :130` attribute the region and structured rules to `RegionLower.lean` /
  `StructuredLower.lean` when since packet D3 their tagged definitions are in
  `Skeleton.lean:320-361` (only `dispatch-fallback` is still in
  `StructuredLower.lean:32`). `generated/lowering-coverage.tsv`'s `input` digest
  list covers `Lower.lean` and `EffectV4.lean` but not `Skeleton.lean` or
  `SkeletonRender.lean`, where 21 of the 29 tags now live. None of this changes a
  conclusion above; all of it is a separate repair.
