# Term runtime: state, interpreter and evaluator

Status: FROZEN / GREEN in the working tree, R3 and R4 together at the owner's
request, base `c462cd1`. The owner also authorized R2's control-boundary
correction on 2026-09-06. Design and evidence:
`docs/research/2026-09-06-r3-r4-implementation.md`. Amended for P1b and P2
(2026-09-06, from `a1fb467`) under the frozen bounded design of
`docs/research/2026-09-06-p0-fable-record.md` §4: the term counts what the
corrected frame machine counts, and the frame machine's corrected clauses are
the host's on the checkpoint table of that record. The delivery review at
`acfc2fc` found remaining source discrepancies D4–D7; that checkpoint's green
gates do not establish their closure or P3. The owner authorized their repair.
The D7 amendment uses the existing success guard for `termCore.yieldBefore`
and evaluates the wrapper in the injecting iteration. Yield parks on the next
counted iteration and resumes through its answer adapter and success guard.

## Owned surface

`Program/InterpR.lean` owns `ScopeFrame`, `RSaved`, the term `FiberCore`,
`RState`/`RFiber`/`RInterp`, direct synthesized-program denotations and
`interpR`. `Program/EvaluateR.lean` owns saved-slot delivery, the local
evaluator and its instance. `Program/RuntimeR.lean` owns loading, replay,
observation, sufficiency and behavior at the term instance. The R1/R2 packets
own `Body`, the control signature, denotation and control erasure.

Canonical syntax remains `Eff`. The term and its saved continuation functions
are the existing higher-order semantic carrier, not a serializable document.
The store type, Completion tape, machine bookkeeping and command loop are
the existing declarations. P1/P2 and the authorized source repairs amend the
existing compiler and shared machine; they do not add another program IR.

## Execution contract

`loadR e fuel choices` loads `denoteR e e (rootPoint fuel choices)` as fiber 0
over empty stores and context. `interpR e` resolves addressed bodies
structurally at their points (`denoteAt`); there is no unfolding budget, and
the compile fuel of the load is the only budget. `replayR` uses the existing
`replayEval` with `termEvaluatorFor e`. `obsR` is the existing exits-and-stores
observation.

An operation whose answer is a value installs its continuation directly
(`answerWith`): the store operations, the identity, context, child-snapshot,
observer, run-in, fork and scoped-fork arms, and the two checkpoints `suspend`
and `sync`. An operation whose answer arrives as code through the shared loop
saves its continuation in the operation-answer adapter slot `ScopeFrame.answer`
(`saveAnswerR`), which is distinct from the lexical `resume` boundary of a
source handler: yield, await, join, the interrupts, the awaits of children,
race, mask, scope close, race cancel and async. Delivery rule: when the pop
reaches an answer slot with an exit it runs the saved continuation inside the
pop, and continues the walk when the result is `pure` or an `unguard` marker;
any other code becomes the fiber's current program. This is why the term
spends exactly the frame's counted steps on an answered operation, and the
whole reason the R4 term counted more (`E4-RTERM-CE-006`).

Source handler boundaries stay on the saved stack; failure skips ordinary
handlers while an interruption is pending and the fiber is interruptible.
Cleanup masks and restoration run in saved-stack order. `finishFinalizer`
restores the cleanup's mask after successful cleanup. Under the D4 OnExit
amendment, cleanup failure instead passes the ordinary success guard and
restores the saved mask in the existing pop. A failed body alone adds the
inner cause-combining failure guard, matching `onExitPrimitive` and
`combineFinalizerCause` (`internal/effect.ts:3800-3804,4019-4030`). The four
immediate success/failure cases must count 5, 6, 4, 6, and the budget-6
failed-body witness must park, as actual printed code does. The focused and
full checks pass, including 24 actual-emission host views (source-repairs §11).
The scoped amendment in source-repairs §12 uses one counted entry that allocates
the scope and installs context together, then the existing OnExit guard around
the eager body. Its callback restores context and cached budget fields before
unsafe close, during that same delivery. No returned effect bypasses the §11
wrappers; a returned effect uses the shared `finalizerR` wrapper. State/order
come from `scopeCloseSnapshot` on both representations. Multiple-finalizer
timing remains open. The store step uses the shared `answered`/`deliver` split:
Deferred resumes happen before delivery checks deferred interruption and runs
the scoped callback. The production proof/gate checks pass: 282 jobs and a fresh
276-module / 39,690-declaration audit, with the existing trust boundary, plus
forced census and the regenerated nine-program truth differential. Multiple
finalizer timing remains open under the D4/D6 obligation above.

Generators and loops are runtime operations with first-order slots
(`E4-RTERM-CE-007`). `FiberOp.gen` pushes `ScopeFrame.iter` with the generator's
name and answers the first walk of `walkR` (the term instance of the compile's
`runStmts`, over `blockAt`, `blockExit` and `loopExit`); each later yield is
answered inside the pop, where the walk's `done`, `halt` and `resume` results
finish the generator, fail it, or re-push the slot with the next point.
`FiberOp.loop` pushes `ScopeFrame.loop` with the loop's name and cursor and
answers the first body; the pop steps the cursor, tests it, and either re-pushes
the slot with the next body or finishes with the loop's result. Neither entry
unfolds the source in the denotation; a generator whose scan budget is spent
stays at the walk's frontier under its slot.

Direct synthesized shapes cover the store's seven finalizer alternatives,
sequential and parallel close chains, race settling, the four cancel cases,
and Completion's exit and Ref-read programs. The two non-source body forms
are `Body.fin` and `Body.raceCleanup` (source-repairs §16, D6a: the settled
race's masked cleanup names the race, and its live set is read when the
cleanup runs, not when the winner was accepted; the synthesized
`Body.interruptFibers` list is gone). The scout's assertion that all of
`progOf` was six atomic cases was inaccurate: the source has additional
compound declared programs. This runtime needs the named shapes above, not
a translation of every `ProgName` or arbitrary named primitive code.

Compile, missing-choice and unsupported-source frontiers, and the generator
walk's scan exhaustion, never receive an answer. Their local step retains the
term and continues until the shared command budget stops the run, so later
tape decisions do not cross that unresolved command boundary. They are not
failures or unknown-scope errors. Unknown fiber/scope requests keep the
reference machine's `Stuck` outcome.

## Shared fiber actions (P1b, 2026-09-06)

D5 construction amendment (2026-09-06): the public frame API selects
`evaluatorFor e`; term replay, sufficiency and behavior select
`termEvaluatorFor e`. Both obtain the current completed exits through
`RunMachine.completedExits`. `interpAt` / `interpRAt` refresh source callback,
suspension, generator, loop and finalizer construction, while eager addressed
mask/fork bodies keep their earlier captured view.

`evaluateRawR` owns one counted local operation. `evaluateR` prepares
administrative construction queries before it and uses `prepareIterR` to
prepare newly returned code. An `answered` result is left pending until
`Cmd.deliver`, after nested Deferred resumes. Preparation uses structural
recursion over the existing term; no unfolding budget or scheduler is added.

The six actual `Api.print` programs in the D5 probe pass 36 bounded views
against the pinned TypeScript host: three scheduling budgets, initial and
flushed observations, counts and selected exits. Frame/term observations,
saved controls and both command-sufficiency receipts also pass in the tracked
runtime battery. These were the finite D5 checks; the general P3 relation was
subsequently proved as recorded below. Public handle integration, the straight-run proof port and the full D5
repaired-tree gate pass: 282 jobs, 276 modules / 39,483 declarations at the
unchanged ceiling, forced census and the nine-program emitted truth battery.
The remaining source repairs at that D5 checkpoint were addressed in §§16–20;
current open target obligations are listed in the P3/P4 section below.

`Machine/Fibers.lean` now carries `FiberAction`, the ordinary `withFiber` arms and the
two parks the alphabet spells, generic in the fiber core and in how an instance installs
a value answer (`FiberAction.Answer`, default `coreAnswer`). The term evaluator's arms
for `getId`, `getContext`, `setContext`, `snapshotChildren`, `dropObservers`, `runIn`,
`fork`, `forkIn`, `forkScoped`, `refuse`, `closeScope`, `interrupt`, `interruptAs`,
`interruptScoped`, `interruptAll`, `awaitAll`, `awaitAllFailFast`, `awaitNewChildren`,
`cancelRace`, `raceAll`, `yieldNow` and `await` are those helpers on the fiber that has saved its
continuation slot; no term behaviour changed, and `RuntimeRReference`'s 75 expectations
and the comparisons below are unchanged. `RuntimeRContract` proves the frame machine's
arms equal to the helpers under `coreAnswer` (`frame_getId` … `frame_join`), by `rfl`
or by splitting the arm's scrutinee. The frame arms themselves are not rewritten to call
the helpers, so no clause or handle proof over `evaluatePrim` changed; the mask, async
and store arms stay instance-specific (the term's async derives its cancel name from
the registration). Sharing the code does not validate an arm against rc.112: the
source citations stay on the frame arms.

## Checked obligations and limits

Universal equations pin the loaded code and observation, Completion decoding,
body resolution, pure/store/frontier steps, the delayed store delivery and the
two checkpoint steps (`evaluateR_suspend`, `evaluateR_sync`).
`BehR_fuel_irrelevant` instantiates the existing sufficient-command-budget
theorem with the loaded code fixed. It does not equate loads made at different
compile fuel.

`RuntimeRReference` holds 75 reference-machine expectations fixed before term
execution. `RuntimeRContract` compares explicit runs over those same source
programs and decision tapes, including suspended intermediate states. Its P2
Lockstep section runs the term and the corrected frame machine on the P0
record's shapes (a scoped context, a generator loop, a cursor loop, a
two-yield generator, fork/join, a Deferred, a race, masks, catches, exits and
the store forms) and pins equal exits and stores, equal command counts per
fiber and equal least command budgets on 38 shapes; the audit's ten local
command pairs; the host's counts on the corrected exit, generator and loop
shapes; the budget-two witnesses (sync, suspend and the skipped catch park on
both machines; the folded exit finishes); the budget-six Completion witness;
a chain of 1100 allocations that yields at the same point on both machines
with the same heap and finishes after the flush; and the scanner and compile
frontiers left unanswered. `entry_is_counted` and `store_step_rel` inhabit
the local outcome/command relation on the store step. `RuntimeRShapesContract`
checks direct synthesized shapes, generator/loop and handler fixtures, and a
completing sync interrupted by its own due resume. These are finite checks.
R5 and the general simulation remain future work; no theorem compares
arbitrary frame and term executions, and the count agreements are pinned per
shape, not derived. Nothing here proves correspondence with a TypeScript/OCaml
host beyond the host table of the P0 record, and nothing changes a runtime
coverage number.

The final-pop correction (2026-09-06) retains `frameExitState f.frame` in
`finishFrame`'s finished branch, reusing the same `getCont` demand and skip
mode as the current exiting operation. `finished_pop_state` freezes that
exact returned iteration. `pending_finish_controls` pins the restored mask,
drained stack and cleared deferred flag while both stored exits are still
absent and the same finish/drain commands remain. The comparison now checks
masks on all fibers. `frameExitState_keys` supplies the handle-preservation
premise; the straight agreement theorem retains its public observation and
command bound. The former terminal-only mask exception is retired.

Named boundaries, also recorded in `Test/Counterexamples/REGISTER.md`:

- `RSTATE-FB-IDENTITY`: the semantic saved state has no content identity,
  serialization or decidable equality; source identity remains first-order.
- `RSTATE-FB-ONSUCCESS-NAME`: the core's named composition accepts only the
  `restore` name produced by the shared exit path; other names refuse.
- `RSTATE-FB-EVALUATOR-FIELD`: frame-only `contA`, `contE`, `parkOf`,
  `withFiberOf` and `syncState` are unused stubs. Since P2 `iterNext` and
  `loopBody` are the generator walk and the addressed loop body, and the
  addressed `.body` case of `suspendBody` is used and implemented.
- `RSTATE-FB-STORE-CODE`: Deferred code manually inserted outside the source
  Completion profile is left at an unsupported frontier; the decoder is not
  a general primitive interpreter.
- `RSTEP-FB-PROTOCOL` (retired 2026-09-07 by the P3 walk agreement): a cleanup-end
  marker delivers the finalizer's exit through the saved slots, restoring the mask at
  the `finalizerMask` slot it meets, exactly as the frame's `Prim.ofExit` restores at
  the `setInterruptible` frame; outside any slot it is the fiber's exit, never `badName`.
  Generated `onExitR` pairs the markers.
- `RSTEP-FB-FRONTIER`: missing work stays unanswered.
- `RSTEP-FB-SIMULATION` (retired 2026-09-07 by `run_eq_ref`): general frame/term
  simulation is proved on every program, budget, tape and choice list, with the
  classification, the whole observation and both sufficiency receipts equal; see the
  P3/P4 section below.
- `RSTEP-FB-HOST`: `run_eq_ref` relates the two Lean machines. Correspondence with the
  TypeScript/OCaml host is the finite pinned evidence of the probes and the truth gate,
  not a theorem.

Acceptance: focused batteries and `#print axioms`, then `lake build Effect4
Test` with every battery reachable from `Test/All.lean`; semantic/test ceiling
`[propext, Quot.sound]`, no new allowances. Run the forced runtime-census
drift gate after integration. The owner stages and commits.

Verified 2026-09-06 (R3/R4): `LEAN_NUM_THREADS=3 lake build Effect4 Test`
passed 282 jobs, 276 modules / 38,771 declarations at `[propext, Quot.sound]`.
Verified 2026-09-06 (P2, the same day, from `a1fb467`): the same gate passed
282 jobs, and the fresh `Test/All` audit checked 276 modules / 39,183
declarations at `[propext, Quot.sound]`. The existing implementation
exceptions remain 7 modules / 41 exact names. The forced census drift check
and `git diff --check` pass. Exact logs and remaining obligations are in the
research receipts above. No files are staged.

Source-repairs §20 (2026-09-07): `forkScoped` compiles to its wrapper
(`compileEff_forkScoped`: `OnSuccess` over the counted `Scope` service read, whose
continuation `forkScopedIn` is `forkIn` on the answered handle, `contAOf_forkScopedIn`,
`withFiberOf_forkInAt`), and the term denotes the node as the same read bound to
`forkIn`. The multiple-finalizer close is `scopeCloseFinalizers`' generator on both
sides (`closeWalkR`, `closeSeqStepR`, `exitR`; the frame's `ProgName.closeWalk` through
the stores' `iterNext`), so the four §20 rows (`forkScopedDone`, `seqOne`, `seqTwo`,
`parTwo`) run in lockstep at the host's counts `[8, 1]`, `[19, 4]`, `[38, 4, 4]`,
`[18, 4, 4, 6, 6]` with equal sufficiency (`RuntimeRContract` `SourceRepairs20`;
`RuntimeRReference` row 16 pins the exits, the parallel daemons interrupting in close
order). `frame_ambientScope` and `frame_closePar` are the two new hook identities.

Numeric fiber IDs (E4-CHECK-CE-010): `RunInterp.fiberIdValue` supplies the numeric
getId result (`internal/effect.ts:1092–1100`); `fiberValue` remains the handle
returned by forks. `native_id_value` fixes both encodings for every chosen ID.
`getIdSucc` is admitted and readable, and both runtimes return Nat 1 for the
logical root ID 0. This does not assert equality with the host process-global
ID allocator; host ID realization remains an explicit target boundary.


## P3/P4 accepted judgments and open host work (2026-09-07)

The coordinator independently checked the P3/P4 implementation at base `acfc2fc`
plus the reviewed working changes. This section owns the accepted statements;
`docs/research/2026-09-07-p3-p4-audit.md` owns the review evidence and
`2026-09-06-wave2-synthesis.md` owns the next work order.

`Effect4.Program.Sched.run_eq_ref e fuel tape choices` has no premise. It
compares `Api.replay` with `replayR` at the same coupled compile/command budget:
classification and `obs` agree, where `obs` contains every fiber's identifier
and optional exit in machine order, plus the whole `Stores` value. It does not
compare trace events or execute a TypeScript host. `replay_rel e cfuel fuel tape
choices` supplies the stronger saved-machine relation with independently
quantified compile and command budgets; `suffices_eq_ref` compares the two
command-sufficiency receipts at those separate budgets. The concrete
`stepAgrees` in `Simulation/Drive.lean` discharges the generic driver's premise.
Local `book_driveState` carries related residual commands; `ReplayResult`
itself does not contain a residual-command list.

`straight_ref e fuel hs hd hfuel` uses exactly `Straight e = true`,
`depth e ≤ fuel` and `2 * steps e + 6 ≤ fuel`. At that same fuel and
`[Api.evaluate, Api.flush]`, the term replay finishes with the single root exit
and the whole store supplied by `meaning e [] Stores.empty`.
`straight_sufficient` proves that budget sufficient, and `straight_beh` gives
the observation through that receipt. The proof reuses the frame-side
`replay_Mexit` and `obs_Mexit`; it introduces no second straight runner.

The full compiled-declaration gate must continue to accept these declarations
and their dependencies at `[propext, Quot.sound]`, with the existing exact
rendering exceptions unchanged. `SimulationContract` is reachable through
`RuntimeRAxiomReport`. Its finite guards supplement the universal judgments.

Current source/target limits remain explicit:

- `E4-CHECK-CE-013`: `Deferred.make()` lacks the type arguments needed for the
  native profile's declared error type; the actual emitted failure composition
  still fails strict TypeScript checking although `ts/eff` typechecks.
- `E4-CHECK-CE-014`: two finite interrupt-all host cases use a pair where the IR
  typing rule demands a list. They are not well-typed admission evidence.
- `E4-CHECK-CE-015`: admitted printed scope/fork forms are outside the current
  reader's image. Exact round-trip statements retain their readable premise.
- `E4-CHECK-CE-016`: repeated execution of one scoped-fork point reuses its
  registration key. The tracked `ScopeRegistrationCollision` witness retains
  the current bad result: two iterations leave the first child live on both
  Lean machines, while pinned Effect interrupts both. The one-iteration
  control passes and command fuel is sufficient. This remains a required
  source-conformance repair, not an exception to the arbitrary-composition
  goal and not a refutation of the frame/term judgment.

P3/P4 proof acceptance therefore permits a milestone commit, not a claim of
host-wide correspondence or readiness of every typed emission. V1 remains
unimplemented. Any registration repair must retain the witness, amend its
expected result, prove key freshness over repeated execution/removal, and
recheck the same P3/P4 statements and gates.
