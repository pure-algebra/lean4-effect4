# Term runtime: state, interpreter and evaluator

Status: FROZEN / GREEN in the working tree, R3 and R4 together at the owner's
request, base `c462cd1`. The owner also authorized R2's control-boundary
correction on 2026-09-06. Design and evidence:
`docs/research/2026-09-06-r3-r4-implementation.md`.

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

`loadR e fuel choices` loads `denoteR e fuel e (rootPoint fuel choices)` as
fiber 0 over empty stores and context. `interpR e fuel` resolves addressed
bodies with that unfolding budget. `replayR` uses the existing `replayEval`
with this instance. `obsR` is the existing exits-and-stores observation.

Every suspended operation saves its continuation before the shared loop
resumes it with code. Source handler boundaries stay on the saved stack;
failure skips ordinary handlers while an interruption is pending and the
fiber is interruptible. Cleanup masks and restoration run in saved-stack
order. `finishFinalizer` restores the cleanup's mask before the enclosing
continuation proceeds. `scopedR` restores the old context before closing its
scope. The store step uses the shared `answered`/`deliver` split: Deferred
resumes happen before delivery checks deferred interruption.

Direct synthesized shapes cover the store's seven finalizer alternatives,
sequential and parallel close chains, race settling, the four cancel cases,
and Completion's exit and Ref-read programs. The two non-source body forms
are `Body.fin` and `Body.interruptFibers`. The scout's assertion that all of
`progOf` was six atomic cases was inaccurate: the source has additional
compound declared programs. This runtime needs the named shapes above, not
a translation of every `ProgName` or arbitrary named primitive code.

Compile, unfolding, missing-choice and unsupported-source frontiers never
receive an answer. Their local step retains the term and continues until the
shared command budget stops the run, so later tape decisions do not cross
that unresolved command boundary. They are not failures or unknown-scope
errors. Unknown fiber/scope requests keep the reference machine's `Stuck`
outcome.

## Checked obligations and limits

Universal equations pin the loaded code and observation, Completion decoding,
body resolution, pure/store/frontier steps and the delayed store delivery.
`BehR_fuel_irrelevant` instantiates the existing sufficient-command-budget
theorem, with the initial code and its unfolding budget fixed. It does not
equate loads made with different denotation budgets.

`RuntimeRReference` holds 75 reference-machine expectations fixed before term
execution. `RuntimeRContract` compares explicit runs over those same source
programs and decision tapes, including suspended intermediate states.
`RuntimeRShapesContract` checks direct synthesized shapes, generator/loop and
handler fixtures, and a completing sync interrupted by its own due resume.
These are finite checks. R5 and the general simulation remain future work;
no theorem compares arbitrary frame and term executions or automatic yield
counts. Nothing here proves correspondence with a TypeScript/OCaml host or
changes a runtime coverage number.

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
- `RSTATE-FB-EVALUATOR-FIELD`: frame-only `contA`, `contE`, `iterNext`,
  `loopBody`, `parkOf`, `withFiberOf` and `syncState` are unused stubs. The
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

Verified 2026-09-06: `LEAN_NUM_THREADS=3 lake build Effect4 Test` passed
282 jobs, 276 modules / 38,771 declarations at `[propext, Quot.sound]`.
The existing implementation exceptions remain 7 modules / 41 exact names.
The forced census drift check and `git diff --check` pass. Exact logs and
remaining obligations are in the research receipt above. No files are staged.
