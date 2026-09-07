# Term runtime: state, interpreter and evaluator

Status: FROZEN / GREEN in the working tree, R3 and R4 together at the owner's
request, base `c462cd1`. The owner also authorized R2's control-boundary
correction on 2026-09-06. Design and evidence:
`docs/research/2026-09-06-r3-r4-implementation.md`. Amended for P1b and P2
(2026-09-06, from `a1fb467`) under the frozen bounded design of
`docs/research/2026-09-06-p0-fable-record.md` §4: the term counts what the
corrected frame machine counts, and the frame machine's corrected clauses are
the host's on the checkpoint table of that record.

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
the existing declarations. No machine/compiler/store definition is changed.

## Execution contract

`loadR e fuel choices` loads `denoteR e e (rootPoint fuel choices)` as fiber 0
over empty stores and context. `interpR e` resolves addressed bodies
structurally at their points (`denoteAt`); there is no unfolding budget, and
the compile fuel of the load is the only budget. `replayR` uses the existing
`replayEval` with this instance. `obsR` is the existing exits-and-stores
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
restores the cleanup's mask before the enclosing continuation proceeds. A
scoped body is spelled as the compile spells it: a `scopeMake` under a success
boundary, then `onExitR` with the context read, the context set and the scope
close, so the old context is restored before the scope closes. The store step
uses the shared `answered`/`deliver` split: Deferred resumes happen before
delivery checks deferred interruption.

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
are `Body.fin` and `Body.interruptFibers`. The scout's assertion that all of
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

`Machine/Fibers.lean` now carries `FiberAction`, the ordinary `withFiber` arms and the
two parks the alphabet spells, generic in the fiber core and in how an instance installs
a value answer (`FiberAction.Answer`, default `coreAnswer`). The term evaluator's arms
for `getId`, `getContext`, `setContext`, `snapshotChildren`, `dropObservers`, `runIn`,
`fork`, `forkIn`, `forkScoped`, `refuse`, `closeScope`, `interrupt`, `interruptScoped`,
`interruptAll`, `awaitAll`, `awaitAllFailFast`, `awaitNewChildren`, `cancelRace`,
`raceAll`, `yieldNow` and `await` are those helpers on the fiber that has saved its
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

The reference `finishFrame` (`Machine/Fibers.lean:963-964`) returns its
incoming fiber when the final pop finishes. The term evaluator retains the
pop's mask restoration. Therefore some exited fibers retain different mask
bits, although every exit, store, waiting state and live mask in the battery
agrees. The comparison checks the mask while the fiber is live and separately
pins this terminal difference. The fixed `Obs` never includes saved masks.

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
- `RSTEP-FB-PROTOCOL`: a cleanup-end marker outside its saved cleanup mask
  is malformed and produces `badName`. Generated `onExitR` pairs the markers.
- `RSTEP-FB-FRONTIER`: missing work stays unanswered.
- `RSTEP-FB-SIMULATION`: general frame/term simulation and step-cost accounting
  are outside these two implementation steps.
- `RSTEP-FB-TERMINAL-MASK`: an exited fiber's retained mask bit is not equated;
  the reference discards its final pop state, as pinned by two negative controls.

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
