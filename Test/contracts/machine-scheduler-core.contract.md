# Shared scheduler core contract

D1 separates code, saved execution state and frame-event payload. The existing
records take these parameters; the external decision tape does not. The default
instances are the existing Prim, FrameFiber and FrameEvent families.

`FiberCore` supplies saved-state operations and small code constructors.
`FiberEvaluator` supplies one evaluation step. These are interpreter parameters,
never stored program syntax. The production scheduler has one command loop,
shared by both representations; it does not require equality on code or saved
state. Canonical application programs remain the first-order `Eff` data.

The existing splitting, settled-loop stability, task/flush stability and
`replay_stable` laws quantify over the chosen core and evaluator. The observation
functions also accept arbitrary code and saved-state types. The concrete frame
clauses and `run_eq_meaning` retain their statements, except for W1's documented
receipt conditions at flush boundaries.

The D7 source correction adds `FiberCore.yieldBefore : κ → κ`: the code
constructor for rc.112's `flatMap(yieldNow, () => previous)`
(`internal/effect.ts:647-655`). Injection installs that code and the evaluator
runs it in the already counted iteration. The frame instance uses the
constant-continuation variant of OnSuccess; the term instance uses its existing
success guard. The ordinary Yield arm owns parking and success resumption.
No new saved-state field or command constructor is required by this correction.

The final-pop correction retains the existing `getCont` walk's saved state
when a frame step finishes (`internal/effect.ts:688-697`). The pending
`Cmd.finish` boundary therefore sees the restored mask and drained stack.
`RuntimeRContract.finished_pop_state` freezes the exact returned iteration;
this changes no shared command, operation count or external decision.

The D6a source correction (source-repairs §16, 2026-09-07) adds
`RunInterp.parkCode : ParkKind → κ`, the code that names a park (the join modes
and the new `ParkKind.race id`), and one delegating outcome, `Outcome.commands`:
`settle` stores the returned fiber, keeps it running and runs precisely the
iteration's nested commands before the rest of the queue. The race entry returns
`parkCode (race id)` and continues; evaluating that code is the counted Async
registration, which runs `[launch id, registrationDone id yielding]`. The parked
branch of `settle` now also clears the guard and loops when the fiber carries a
deferred interrupt (`internal/effect.ts:662-667`). The stores and the native
interpreter answer `parkCode` through their park thunk, the term instance through
`FiberOp.raceRegister`, and the Layer profile with its unused-race refusal. No new
saved-state field; two new commands, `enrollRace` and `registrationDone`.

The D6b source correction (source-repairs §19, 2026-09-07) adds three code makers
to the interpreter — `interruptCode target` (the public `fiberInterrupt`),
`interruptAsCode target who` (`fiberInterruptAs`, what the public interrupt's
`withFiber` returns) and `interruptAllCode targets` (`fiberInterruptAll`, the
child-exit middleware's program) — and `ParkKind.awaitAll targets`, the
`fiberAwaitAll` park. The interrupt arms delegate through `Outcome.commands`:
`interruptTarget` records one target and runs it when idle, `afterInterrupt`
constructs `asVoid` of the await afterwards and continues the entry with `loop`,
`raceCancel` walks a race's live Set. `spawn` no longer tracks; `trackChild` does,
after the child's immediate run. The exit path publishes the exit, then one
`observe` command per observer in index order, then `exitDone`; a fiber with no
observer is cleared in the same step, so the straight fragment's exit cost is
unchanged. The middleware re-enters the fiber with `evaluate`, a new counted
entry. Six new commands, no new event or saved-state field.

`SchedulerCoreContract` executes the actual `Effects.Program` carrier with a
store operation and a yield operation. Its answer adapter keeps the continuation
while the shared dispatcher resumes with success. It exercises the
shared loop, yields, resumption, token checks, Completion answers, interruptions
and the generic fuel laws, including a check that injection actually parks.
This is finite integration evidence;
`CORE-FB-SIMULATION` reserves the real `evaluateR`, `CodeMeans`/`FrameMeans` and
simulation obligations for later slices.

`CORE-FB-TRACE`: an arbitrary evaluator may erase the trace. A checked fixture
does so, making the trace shorter at a larger budget. Generic trace growth is
therefore conditional on a command-step trace premise in
`drive_extends_of_step` and `drive_trace_mono_of_step`. The frame instance proves
that premise in `driveStep_grows`; its unconditional replay-order theorem remains
`replay_obs_mono`.

Receipts: `Test/Machine/Runtime/SchedulerCoreAxiomReport.lean`. No new trust
exceptions, host claims, serialized algebra programs or second scheduler.

Source-repairs §20 (2026-09-07): `FiberCore` gains `pushIterator`, the generator's
own frame pushed under an effect a command yields on its behalf (the parallel
close's await); the algebra fixture, which has no generator frames, takes it as the
identity. `RunInterp` gains `scopeValue` (a scope handle as a value) and
`closeDoneName` (the parallel close generator's name under its await); the fixture
answers `0` and `()`.

## Table-aware agreement (DI-57): the statement

`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean`) is the frame machine's
replay against the term reference's, and it takes **no table and no oracle
answers**. Its docstring now says so. `Api.replay` takes both. The theorem is
therefore an internal agreement at the empty table with no external answers, and
it is not a table-aware claim and not a host claim.

The target proposition, which no proof yet discharges, is the one scout B
elaborated (`docs/research/2026-09-09-scout-proof-statements.md` §6, an untracked
working note), verbatim:

```lean
def RunEqRefTableStatement
    (reference : NativeEff → Nat → List Api.Decision → List Bool →
      List (Completion Val Err Defect FiberId Ann) → RowTable → RReplay) : Prop :=
  ∀ e fuel tape choices answers table,
    (Api.replay e fuel tape choices answers table).outcome =
      classify (reference e fuel tape choices answers table) ∧
    obs (Api.replay e fuel tape choices answers table).machine =
      obsR (reference e fuel tape choices answers table).machine
```

It is a proposition awaiting a reference implementation: `reference` is an explicit
parameter because today's reference does not have those two arguments. The
comparison it makes is the current internal observer's — every fiber's exit and the
whole stores — and nothing else.

Four gaps on the reference side, each a place the reference does not yet do what
the frame machine does with a non-empty table:

* external-row registration — `src/Effect4/Laws/Program/InterpR.lean:313`;
* evaluator selection — `src/Effect4/Laws/Program/EvaluateR.lean:342`
  (`termEvaluatorFor` calls `interpRAt` internally instead of using an interpreter
  supplied to replay, so a table-aware interpreter cannot be passed in);
* the external answer's conversion and allocation —
  `src/Effect4/Program/Compile.lean:1410`;
* the prepared answer — `src/Effect4/Program/Compile.lean:1439`.

Scout B's counterexample fixes the size of the gap: one asynchronous external row,
request `7`, reply `9`, fuel `40` and the usual `[evaluate, flush]` tape gives the
frame machine `finished` with the oracle drained and the unchanged reference
`frontier` with the reply unconsumed. Two observers disagree, so the statement is
false of today's reference and the repair is a semantic extension, not a
restatement.

The proof is a later slice, after S6b freezes the call protocol: the envelope has
to be the same on both sides before the two machines can be related through it.
The envelope itself is landed and tested (`src/Effect4/Program/Admit.lean`,
`Test/Program/HostSpecContract.lean`); this statement is filed, not proved.
