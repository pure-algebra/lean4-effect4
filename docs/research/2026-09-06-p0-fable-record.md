# P0 record: the source/print/compiler checkpoint table and the frozen bounded design

Claude Fable, 2026-09-06, from clean `a1fb467`. This record closes the five P0
deliverables of the [candidate brief](2026-09-06-p0-checkpoint-candidate.md) §5 and
freezes the bounded design that P1a, P1b and P2 implement. The
[synthesis](2026-09-06-wave2-synthesis.md) owns the work order; this record owns
the P0 evidence, the design, and the packet amendments the implementation lands.
Nothing under `src/`, `Test/` or `generated/` changed for P0; the evidence is under
`docs/research/probes/p0-fable/`.

Landing (2026-09-06, same seat): P1a, P1b and P2 are green on the whole-tree gate at
`[propext, Quot.sound]`. P2's gate: `lake build Effect4 Test` 282 jobs; the fresh
`Test/All` audit 276 modules / 39,183 declarations, implementation boundary 7 modules /
41 declarations; forced census PASS (137 rows); `git diff --check` clean. The packet
amendments of §7 and the register rows are in the tree; `E4-CHECK-CE-004`–`007` stay
RESERVED for the machine-side slices. The 38 lockstep guards, the ten command pairs, the
budget-two and budget-six witnesses and the 1100-allocation chain of
`Test/Program/RuntimeRContract.lean` are the term-side evidence; the host table of §1 is
the host-side evidence. Nothing is staged.

## 1. Evidence produced

| File | What it is | Result |
| --- | --- | --- |
| `probes/p0-fable/host_table.ts` | 41 public expressions, one per printer clause on its smallest fixture, executed against the vendored pin with a `Tracer.context` hook recording every primitive `runLoop` evaluates (`internal/effect.ts:653-655`); a bounded dispatcher-callback drain; a budget-2 phase trace | `bun` exit 0; all 14 pinned facts hold; `host-results.json` |
| `probes/p0-fable/p01_phases.lean` | a scratch term machine (own signature, saved state, evaluator, structural denotation, generator walk) on the existing shared loop; 20 lockstep shapes, the corrected exit/gen/loop shapes against the host numbers, budget-2 witnesses, interrupted cleanup, scanner exhaustion, the local relation | exit 0; every `#guard` holds; receipts at or below `[propext, Quot.sound]`; `p01.log` |
| `probes/p0-fable/p02_frame_table.lean` | frame-machine and current-term counts on the host rows that the phase prototype does not cover | exit 0; `p02.log` |

Commands, serialized under `.lake/LANE.lock` with `LEAN_NUM_THREADS=3`:

```text
bun docs/research/probes/p0-fable/host_table.ts
lake env lean -M 3072 docs/research/probes/p0-fable/p01_phases.lean
lake env lean -M 3072 docs/research/probes/p0-fable/p02_frame_table.lean
```

Receipts printed by p01: `store_step_rel` `[propext, Quot.sound]`; `denoteP`, `popP`,
`evalP` `[propext]`; `walkP` `[propext, Quot.sound]`. These are finite executions and
one universal local step; no simulation theorem is claimed.

## 2. The checkpoint table

Columns: the printer clause (`Codegen/Print.lean`), the primitives the host evaluates
for it (`host-results.json`, `ops`, one entry per `runLoop`), the frame compile clause
(`Program/Compile.lean`) with the frame count, the current term count (R4 evaluator),
the P2 term count from the prototype, and the verdict. Counts are the root fiber's
`currentOpCount` when the run settles; `a | b` are two `runLoop` entries.

| `Eff` form | Printed as | Host primitives | Frame (clause; count) | Term R4 | P2 term | Verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `succeed` | `Effect.succeed(v)` | `Success` | `Prim.success` (`:286`); 1 | 1 | 1 | agree |
| `fail`, `failCause` | `Effect.fail(e)`, `Effect.failCause(c)` | `Failure` | `Prim.failure`; 1 | 1 | 1 | agree |
| `yieldError` | the yieldable error itself | `YieldableError Failure` (`core.ts:572-575`) | `Prim.yieldableError` (`:298`); 2 | 1 | 2 | term corrected by a checkpoint marker |
| `sync` (pure) | `Effect.sync(() => v)` | `Sync` (answered, uncounted delivery, `:929-936`) | `Prim.sync (pure p)` (`:302`); 1, 6 commands | 1, 5 commands | 1, 6 commands | term corrected: `answered` phase |
| `suspend` | `Effect.suspend(() => b)` | `Suspend` then the body (`:939-946`) | `Prim.suspend (body child)` (`:303`); 2 | 1 | 2 | term corrected by a checkpoint marker |
| `perform` (sync row) | `Ref.make(v)` … | `Sync` | `Prim.sync (op o)` (`:304-312`); 1, 7 commands | 2, 8 commands | 1, 7 commands | term corrected: no answer slot |
| `bind` | `Effect.flatMap(a, (a0) => b)` | `OnSuccess a … b` (`:1684-1688`) | `Prim.onSuccess` (`:319`); bindStore 3, bindTwice 5 | 4, 6 | 3, 5 | term corrected |
| `catchCause` | `Effect.catchCause(b, (a0) => h)` | `OnFailure` (`:2496-2500`); skipped 2, taken 3 | `Prim.onFailure` (`:321`); 2, 3 | 2, 3 | 2, 3 | agree |
| `matchCause` | `Effect.matchCauseEffect(b, {…})` | `OnSuccessAndFailure`; 3 | `Prim.onSuccessAndFailure` (`:322`); 3 | 3 | 3 | agree |
| `onExit` | `Effect.onExit(b, (a0) => f)` | `OnExit b Success OnSuccess f Success` (`:4006-4031`); 5, onExitRef 9 | `Prim.onExit … false` (`:325`); 5, 9 | 6, 13 | 5, 9 | term corrected |
| `exit` | `Effect.exit(b)` | folds an Exit body: `Success` (1); `exitSync`: `Exit Sync Success` (3); `exitYieldError`: 4 (`:3621-3622`) | `Prim.exitFrame` always (`:326`); 3, 3, 4 | 3 | 1, 3, 4 | **D1**: frame corrected in P1a (fold); term corrected |
| `uninterruptible`, `interruptible` | `Effect.uninterruptible(b)` … | `WithFiber` then the body (`:4302-4352`); 2, nested 3 | `Prim.withFiber (act p)` (`:327-328`); 2, 3 | 3, 5 | 2, 3 | term corrected |
| `branch` | `Effect.suspend(() => t ? a : b)` | `Suspend` then the branch; 2 | `Prim.suspend (body p)` (`:329`); 2 | 1 | 2 | term corrected |
| `gen` | `Effect.gen(function*() {…})` | `Suspend Iterator …` (`:1175-1196`, `:1355-1376`): inline 3, resumed 5, loop 11, fail 3 | `Prim.iterator` directly (`:320`); 2, 4, 10, 2 | unrolled: 25 for genLoop | 3, 5, 11, 3 | **D2**: frame corrected in P1a (suspend wrapper); term corrected (runtime generator) |
| `whileLoop` | `Effect.suspend(() => { let a0 = i; return Effect.whileLoop({…}) })` | `Suspend While …` (`:4629-4646`): three iterations 6, zero 3, whileRef 10 | `Prim.whileLoop` directly (`:330-333`); 5, 2, 9 | unrolled: 16 for whileRef | 6, 3, 10 | **D3**: frame corrected in P1a (suspend wrapper); term corrected (runtime loop) |
| `yieldNow` | `Effect.yieldNowWith(k)` | `Yield` parks; the resume evaluates `exitVoid` (`:982-995`): 2 \| 2 | `Prim.yieldNowWith` (`:334`); 2 \| 2 | 2 \| 3 | 2 \| 2 | term corrected |
| `callback` (`Deferred.await`) | `Deferred.await(d)` | `Async`; a completed cell resumes inside the register (`:1120-1126`): deferredImmediate 6 | `Prim.async` (`:335-342`); 6 | 9 | 6 | term corrected |
| `awaitFiber` | `Fiber.join(f)` / `Fiber.await(f)` | live target: `Async \| Success` (4 \| 1); exited target: folded at construction, `Success` (`:767-822`): 4 | `suspend (park (join …))` (`:343-346`): live 4 \| 1; exited 5 | 5 \| 2; 7 | as frame | **D5**: exited join/await; frame arm |
| `withFiber` (`getId`, `getContext`, `setContext`, …) | `Effect.fiberId`, `Effect.context()` … | `WithFiber Success`; 2 | `Prim.withFiber (act p)` (`:347`); 2 | 3 | 2 | term corrected |
| `withFiber (fork …)` | `Effect.forkChild(p, {…})` | `WithFiber`; an immediate child runs on the parent's stack | `withFiber` → `spawn`/`start`; forkJoinImmediate 5 | 7 | as frame less the join (D5) | agree on the fork itself |
| `withFiber (raceAll …)` | `Effect.raceAll([…])` | `WithFiber Async Success`: the winner settles inside the register, the same entry continues (3) | park, then `Cmd.resume`/`Cmd.evaluate` with the count reset: [1, 1] | [2, 1] | as frame | **D6**: immediate settle phase; frame arm |
| `scoped` | `Effect.scoped(b)` | `WithFiber OnExit b Success Success` (`:3938-3948`): 5 | `onSuccess (sync scopeMake) (scopeOpen p)` and three more frames (`:348-350`, `:558-567`): 20 | 28 | mirrors the frame | **D4**: scope protocol; V1 |
| `acquireRelease` | `Effect.acquireRelease(a, (a0, a1) => r)` | ambient-scope registration (`:3971-3987`) | frontier (`:351`) | frontier | frontier | unsupported; V1 |
| `choose` | refused by the printer | — | tape-decided (`:352-356`) | tape-decided | tape-decided | no host form |
| injected yield | — | at the budget: `OnSuccess` (the injected `flatMap`), next iteration `Yield`; the resume entry evaluates `exitVoid` and pops that frame before the saved primitive (`:643-655`) | parks in the injecting iteration; resumes with the saved primitive (`Fibers.lean:826-839`) | as frame | as frame | **D7**: injection phases; frame alphabet |

The budget-2 trace makes D7 exact: `Effect.suspend(() => Effect.succeed(1))` at
`MaxOpsBeforeYield = 2` runs `Suspend OnSuccess Yield | Success OnSuccess Yield | …`
and never finishes, because every resume entry spends its first op popping the injected
frame and its second on the re-injection. The frame machine finishes it after one
flush (`reference_suspend_finishes_after_flush` in the checkpoint audit).

## 3. The discrepancies and where each is fixed

| Id | Fact | Fix | Slice |
| --- | --- | --- | --- |
| D1 | `Effect.exit` returns `exitSucceed(self)` when `self` is already an Exit; the frame always pushes `exitFrame` | `compileEff (.exit b) p` folds to `Prim.success (reifyExitVal ex)` when `headExit (compileEff b (p.child 0)) = some ex`; the same fold in `denoteR` through `inlineYield`, which gains the `exit` clause (`inlineYield (.exit b) p = (inlineYield b (p.child 0)).map (Exit.success ∘ reifyExitVal)`) and keeps `inlineYield_eq_headExit` | P1a |
| D2 | `Effect.gen` is `suspend(() => fromIteratorUnsafe(…))` | `compileEff (.gen _) p = Prim.suspend (EffThunk.body p)`; `suspendBodyAt` on a `gen` node answers `Prim.iterator (EffName.gen p [] false) Val.unit`, the `branch` precedent | P1a |
| D3 | the printed `whileLoop` is wrapped in `Effect.suspend` so each run starts from its initial cursor | `compileEff (.whileLoop initial …) p = Prim.suspend (EffThunk.body p)`; `suspendBodyAt` on a `whileLoop` node evaluates the initial cursor and answers `Prim.whileLoop (EffName.loop p) cursor`; `inlineYield (.whileLoop …) = none` | P1a |
| D4 | `Effect.scoped` is one `WithFiber` that makes the scope object, sets the context synchronously and returns `onExitPrimitive(body, finalizer)`, whose finalizer restores the context synchronously and returns the close effect or `undefined` | needs a `WithFiberAction` arm that allocates in the scope store, sets the context and installs the `onExit`, and a finalizer that restores the context without an op; that is the scope/acquisition protocol the synthesis routes to V1 | V1; register row `E4-CHECK-CE-004` |
| D5 | `fiberJoin`/`fiberAwait` on a fiber that has exited return the exit at construction | the join arm of `evaluatePrim` (`Fibers.lean`, the `ParkKind.join` case) should deliver `exitValue exit mode` in the same counted step when the target has exited, instead of installing it and continuing | machine-phase slice on `Fibers.lean` (coordinator surface); register row `E4-CHECK-CE-005` |
| D6 | an `Async` whose register resumes synchronously continues the same `runLoop` entry (`:1120-1126`); `raceAll` settled by an immediate entrant is that case, and so is any countdown that resumes at once | the race park should resume inline when the launch settles the race before the park returns; today the settle goes through `Cmd.resume` and `Cmd.evaluate`, which resets `currentOpCount` | same slice; register row `E4-CHECK-CE-006` |
| D7 | the injected yield is a pushed `flatMap(yieldNow, () => prev)` frame; the park costs the push and the `Yield`, and the resume pops it in one counted op | the frame alphabet has no frame that returns code; either a `Prim` constructor for the injected continuation (touches every `match` on `Prim`, the handle traversals and the avatar descriptions) or a fiber-level saved primitive answered by a `success unit` resume; the term side can mirror either with a saved slot | same slice; register row `E4-CHECK-CE-007`; the current term keeps the frame's protocol |

D1–D3 are compiler-local and are the P1a corrections. D4–D7 need arms of the shared
machine or its alphabet; this seat records them with their host evidence and does not
edit `Machine/Fibers.lean` or `Machine/Frames.lean` for them. Until they land, the frame
machine is the term's reference on those shapes and the difference to the host is
named, not hidden.

The printer's tuple request (`printRow`, `Print.lean:82-88`) against the host's
two-argument `Ref.set`/`Deferred.succeed` (audit A7) is a target-realization
discrepancy of the emitted text, not of the runtime; it stays with the target lane.

## 4. The frozen bounded design (P2)

The prototype `p01_phases.lean` is the design; production transfers it onto
`RSig`/`RProgram`. What it fixes:

**Operation answers.** An operation whose answer is a value computed in its own arm
(`getId`, `getContext`, `setContext`, `snapshotChildren`, `dropObservers`, `runIn`,
`fork`, `forkIn`, `forkScoped`, `refuse`, and every store operation) resumes its
continuation directly: `current := next v`. No slot is saved. An operation whose
answer arrives as code through the shared loop's `answerWith` (`yieldNow`, `async`,
`await`, the countdown parks, `raceAll`, `mask`, `closeScope`, the loop and generator
entries) saves the operation-answer slot `ScopeFrame.answer (next : ExitV → RProgram)`,
distinct from the lexical handler slot `ScopeFrame.resume kind next`.

**The delivery walk.** `popR` walks the slots as `getCont` does. A lexical slot that
answers installs its continuation's code and stops (a counted step evaluates it, as
the frame machine evaluates `contA`'s code). An answer slot applies its continuation
and, when the result is `pure ex'` or `vis (unguard ex') _`, keeps walking with `ex'`:
that is the frame machine's resume code popping the source frame in the one counted
step that evaluates it. `finishFinalizer ex` restores the cleanup mask and delivers its
continuation the same way. Any other result is installed and stops. The walk is
structural on the slot list.

**Checkpoint markers.** `FiberOp.suspend (at_ : Point)` (answer `Val`) is the counted
checkpoint that returns code: emitted by `denoteR` for `suspend`, `branch`, a valid
`yieldError`, and in front of the generator and loop entries. `FiberOp.sync (value :
Val)` (answer `Val`) is a pure thunk's value delivered through the `answered` phase.
Both erase to `pure` under `controlErasure`, so `denoteR_straight` reads as before.

**Runtime loops and generators.** `FiberOp.gen (at_ : Point)` and `FiberOp.loop (at_ :
Point) (cursor : Val)` (answer `ExitV`) are the initial entries. Their evaluator arms
save an answer slot, then: the generator entry walks with `interp.iterNext (.gen p []
false) unit` and on `resume code next` pushes `ScopeFrame.iter next` and installs
`code`; the loop entry tests with `interp.loopTest`, pushes `ScopeFrame.loop (.loop p)
cursor` and installs `interp.loopBody`. In the walk, `ScopeFrame.iter generator` on a
success calls `interp.iterNext generator v` again and re-pushes itself under the next
name; `ScopeFrame.loop name cursor` steps, tests and re-pushes; a failure skips both,
as the host frames have only `contA`. The interpreter's `iterNext` and `loopBody`
stop being stubs: `iterNext (.gen p pc bind) v` runs the code-parameterized walker
with `denoteR` as the yielded code and `inlineYield` as the fold classifier;
`loopBody (.loop p) cursor = denoteAt root (p.childWith 0 cursor)`. Scanner
exhaustion resumes with a compile-fuel frontier at the exhausted point under an
`iter` slot that keeps the program counter, environment and binding flag; nothing is
answered.

**No unfolding budget.** `denoteR root e p` is structural on `e`; `p.fuel` is the only
budget, spent as `compileEff` spends it. `FrontierReason.unfoldingFuel`,
`ResumePoint.generator`, `ResumePoint.loop`, `denoteGen`, `denoteYield` and
`denoteLoop` go; `ResumePoint` collapses to the point; `interpR` and `loadR` lose the
unfolding argument. Compile-fuel, unanswered-choice and unsupported frontiers stay
unanswered; `FiberOp.frontier (reason) (at_ : Point)`.

**Retained.** `guard_`/`unguard`/`finishFinalizer` and their counted entry;
`deliverR`'s deferred-interrupt check; the handler skip under a pending interrupt; the
false cleanup delimiter; the `asyncFinalizer` slot; `restoreR` on the shared loop's
`restore` name; the `answered`/`deliver` split with due resumes before delivery;
`Body`; the direct synthesized shapes; `Completion` decoding; the terminal-mask
difference (`RSTEP-FB-TERMINAL-MASK`). `scoped` denotes structurally as the frame
compiles it today (`guardR .onSuccess (storeR scopeMake)` then the context/close
frames of `scopedR`), so `FiberOp.scoped` is no longer emitted and is removed; D4
changes both machines together later.

**Counts and commands.** The prototype measures both. Every shape the frame machine
gets right is in lockstep on observation, counted operations and the least settling
command budget (20 shapes, including the six local pairs of `wave2-local/p05`, which
the current term misses on four). The three corrected shapes agree with the host's
counts and with the frame's observations.

**Termination and payloads.** `denoteP` is accepted structurally; `walkP` on its scan
fuel; `popP` on the slot list; the evaluator arms are non-recursive. Saved payloads
are `Point`, `EffName`, `Val` and `ExitV`; only the continuation functions belong to
the semantic carrier, as before.

## 5. The local relation

`store_step_rel` (p01): on a store `sync`, the frame machine's counted step and the
prototype's agree on the `Outcome`, on the residual commands with their code erased
(`CmdShape`), and on the store, for every machine, fiber and continuation with equal
stores. This is the first inhabited clause of the local outcome/command relation the
synthesis asks for; the relation is stated on `Iter` results, not on counters. Equal
counters are a consequence on this clause, not its content. The frame side's
`Outcome.answered` with `[Cmd.drainDue]` or `[]` is matched exactly.

## 6. Consumer inventory for P1a

| Change | Consumers to adjust | Classification |
| --- | --- | --- |
| `compileEff (.exit b)` fold | `Agreement.lean`: `compileEff_exit` (split into fold/frame clauses), `plainCode_compileEff` exit arm, `localRun_compile` exit case (a fold branch through `meaning_exit` and a new `headExit`/`meaning` bridge on plain bodies); `Handles.lean`: `compileEff_keys` exit arm; `DenoteR.lean`: `inlineYield` gains the `exit` clause, `inlineYield_eq_headExit` re-proved; `denoteR (.exit b)` folds | named source correction; exits unchanged in every battery |
| `compileEff (.gen _)` wrapper | `Handles.lean`: `compileEff_gen`, `compileEff_keys` gen arm, `suspendBodyAt_keys`; `Agreement.lean`: `suspendBodyAt_of_at` gains the `gen`/`whileLoop` exclusions (Plain supplies them); `interpOf_keyBounded` unchanged | named source correction |
| `compileEff (.whileLoop …)` wrapper | `Handles.lean`: `compileEff_whileLoop`, `compileEff_keys` whileLoop arm, `suspendBodyAt_keys`; `DenoteR.lean`: `inlineYield` whileLoop clause, `inlineYield_eq_headExit` | named source correction |
| batteries | `CompileContract` (exits unchanged; no count guard), `AgreementContract` (`localAgrees pExit` still finishes: fewer steps), `DenoteContract`, `RuntimeRReference` (exits/stores unchanged), `RuntimeRContract` (frame/term comparisons on gen/while programs stay exit-and-store), `DenoteRContract` (`inlineYield` guards; the R2 unfolding-frontier pins are restated in P2) | unchanged expectations except the named restatements |
| `harness/truth/corpus.json` | `frames` counts of `pGen`/`pLoop` change on regeneration; recorded, never compared | regenerate when the truth gate is next run |
| census | no joined witness names `compileEff`, `suspendBodyAt`, `inlineYield` or `denoteR` | unchanged |

## 7. Packet amendments (landed with the slices)

**`program-denotation.contract.md`** (P1a): item 27's `steps` remains an upper bound;
`compileEff_exit` becomes two clauses; a new lemma states that a plain body whose
compiled head is an immediate exit has that exit as its meaning at unchanged stores.

**`program-denote-r.contract.md`** (P1a, then P2): ENSURES 3 keeps
`inlineYield_eq_headExit` with the new `exit` and `whileLoop` clauses; P2 replaces
ENSURES 1–2 (the budget arms) with the structural equations at positive compile fuel,
keeps 4–6 (erasure now also removes `suspend` and `sync` markers; `denoteR_straight`
and `meaning_denoteR_straight` keep their statements minus the unfolding premise).
`RDEN-FB-UNSUPPORTED` stays.

**`program-sched.contract.md`** (P2): claim 1 lists the four new operations and drops
`scoped`; claim 2 adds the answer types; `ResumePoint` becomes a point.

**`program-runtime-r.contract.md`** (P2): the execution contract gains the answer slot,
the delivery rule, the loop/generator slots and the removal of the unfolding argument;
the finite comparisons are re-pinned; `RSTATE-FB-EVALUATOR-FIELD` shrinks to the
frame-only hooks that remain stubs (`contA`, `contE`, `parkOf`, `withFiberOf`,
`syncState`).

**Register rows** (P1a): `E4-CHECK-CE-001` (exit folding), `E4-CHECK-CE-002` (generator
wrapper), `E4-CHECK-CE-003` (loop wrapper): the frame count was frozen as the host's;
witness: the host table; repair: the compile clauses above. Deferred: `E4-CHECK-CE-004`
(scoped), `-005` (exited join), `-006` (inline settle), `-007` (injection phases), each
with the host trace as witness and the machine-side repair named.

## 8. Remaining frontiers and obligations

Source-address admission (the `Node.at_` premise of introduction), the terminal saved
controls (`E4-RTERM-CE-005`, the deferred bit and stack after exit), the interruptible
finalizer flag restriction, the unfolding of synthesized programs and the pinned-host
connection beyond finite tables remain as the synthesis states them. D4–D7 are new
named host/frame discrepancies with machine-side repairs. The prototype covers no
async, race, scope or child arms; P2 keeps those arms' current protocol with the
answer slot in place of the `.all` resume slot they save today.
