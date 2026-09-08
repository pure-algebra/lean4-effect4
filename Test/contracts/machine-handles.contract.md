# Machine handle contract

Node: C13, `handles_minted`. Implementation: `src/Effect4/Laws/Machine/Handles.lean` (the
invariant at any name and thunk alphabet) and `src/Effect4/Laws/Program/Handles.lean` (the
compiled alphabet and the public statement). Battery and receipts:
`Test/Machine/Runtime/HandlesContract.lean` and
`Test/Machine/Runtime/HandlesAxiomReport.lean`.

## Required statements

1. `Handle` is a fiber id, a Ref key, a Deferred key or a scope id. `RunMachine.keys`
   collects the declared handle positions: every fiber's frame (current primitive and
   stack), pending parks, finalizing and stored exits, observers, children, dispatcher
   tasks and context; each race's host, live entrants, accepted exit and remaining code;
   the armed queue; and the stores (heap values, Deferred
   completions and due resumes, scope finalizer names). The trace is excluded. The
   traversal is generic in the name and thunk alphabets (`nk`, `sk`) and structural on
   `Prim`.
2. `Handle.existsIn` asks the machine's world: a fiber id is one of `m.fibers`, a key is
   below the store's length or names a scope entry (`Val.validIn`'s conditions, one
   handle at a time). `MintedAt nk sk m` says every collected handle exists. It is
   decidable. `Minted (m : Api.Machine)` is `MintedAt` at the compiled alphabet.
3. `KeyBounded nk sk interp` is the contract on the interpreter's hooks: each hook's
   output names only handles its inputs named, and the store hooks (`syncState`,
   `registerAsync`, `dueResumes`, `scopeLinkFiber`, `dropFinalizer`, `closeScope`) grow
   the store and keep every collected handle existing. `stores_keyBounded` proves it for the
   stores' own alphabet; `interpOf_keyBounded` for the compiled alphabet, through
   `compileEff_keys` (the compile names only the point's captured exits and environment), `runStmts_keys`
   (the generator walker keeps to its point's captured exits and environment), `actionAt_keys` (a `withFiber`
   action names only what its terms evaluate to) and `embed_keys` (embedded stores'
   programs carry the stores' keys).
4. Preservation is proved for every helper the command loop reaches: `spawn`, `start`,
   `injectYield`, `evaluatePrim` and each `withFiber` arm, `exitFiber` (the published
   fiber and the counted middleware re-entry), `launchEntrant`, `linkScope`,
   `interruptRecord`, `settle`, `driveStep` — with one lemma per command, the D6b
   commands included (`interruptTarget`, `afterInterrupt`, whose await code is bounded
   by the park's targets or an exit the machine holds, `raceCancel`, `trackChild`,
   `observe`, `exitDone`) — and the three interrupt code makers, each bounded by its
   target handles (`KeyBounded.interruptCode`, `interruptAsCode`, `interruptAllCode`);
   the §20 arms and command (`ambientScope`, whose answered handle the context names
   — `KeyBounded.ambientScope`, `scopeValue` — and `closePar`, whose daemons
   `forkFinalizers_minted` mints one spawn at a time, and `closeParAwait`, whose pushed
   generator name is closed — `KeyBounded.closeDoneName` — over the park's targets);
   the stores' close through `storesCloseScopeUnsafe_keys`, now the walk's
   `ProgName.closeWalk` keys, and the stores' two generator hooks (`closeSeq`'s step
   names the yielded finalizer's program and the shorter order; `closeParDone` names
   nothing), embedded into the native interpreter through `embedStep`;
   `driveState`; then `fireState`, `flushAllState`, `flushRootState`,
   `stepDecisionState` and `replayEval` (`replayEval_minted`). Each receipt also carries
   `World.le`: fibers are only added, stores only grow.
5. `AnswersValid program fuel tape choices` is the tape premise (C15's `TapeAddressed`
   reading): along the replay from the loaded program, every `answerAsync` names handles
   that exist in the machine it answers. It is decidable and is checked where the answer
   lands; replay admission is unchanged. `load_minted` says a loaded program holds no
   handle. `handles_minted`:
   `Minted (Api.load p fuel c) ∧ AnswersValid p fuel tape c → Minted (Api.replay p fuel tape c).machine`.

## Refusals, by name

* The cause's interruptor (`Cause.interrupt (some who)`) is provenance, not a handle:
  `exitKeys (Exit.failure _) = []`. Row `E4-HANDLE-CE-002`: a tape may interrupt from a
  fiber that never existed, and the machine is minted.
* The exit a scope closed with, a race's duplicate winner and unused bookkeeping, and a
  Deferred's waiter targets are excluded. The race's accepted exit is collected because
  the registration return and the guarded resume install `raceSettle race cleanupNeeded
  exit` on the host, and its live entrants because the settled race's cleanup
  (`ProgName.cancelRace race`) interrupts them when it runs; since source-repairs §16
  (D6a) `KeyBounded.raceSettle` is bounded by the accepted exit's keys alone, and
  `KeyBounded.parkCode` by the park kind's keys, where a race park names no handle
  (`ParkKind.keys (race _) = []`). Deferred waiter targets
  become command targets; an unknown target is ignored, and only the separately collected
  completion code can enter a frame. These exclusions are part of the predicate's stated
  boundary, not a claim that every identifier stored anywhere is valid.
* `Val.validIn` alone is the store's view: it says nothing about fibers (row
  `E4-HANDLE-CE-003`), so the invariant asks the machine (`Handle.existsIn`) and reuses
  `validIn`'s conditions for the three store handles.
* A well-typed source program does not certify the replay state (row `E4-HANDLE-CE-001`):
  the external answers of the tape can name anything. The theorem carries the tape
  premise; nothing was added to replay.

## Counterexamples and the ruling

`E4-HANDLE-CE-001`: the well-typed `waiting` program answered with `fiber ⟨7⟩` or
`cell ⟨7⟩` finishes with a handle nothing minted. Ruling: a valid-input premise on the
theorem (`AnswersValid`), not a change to replay admission. The battery shows both
examples fail `AnswersValid` and leave machines that are not `Minted`, and that the same
program answered with a number or with the Deferred it made passes both.

These are statements about the Lean machine. Nothing here says anything about any host.


D5 construction-data amendment (2026-09-06): `Point.keys` includes the value
handles in its captured completed-fiber exits, followed by its environment's
handles. Snapshot lookup identifiers are comparison keys, not dereferenced
handles. `Point.awaitExit_keys` must justify every handle returned by an eager
join/await fold. `compileEff_keys` retains its statement against `Point.keys`;
it no longer claims that environment values alone bound the compiled output.
The root's captured view is empty. Runtime freshness is justified separately:
`RunMachine.completedExits_keys` bounds the projection by the current machine's
keys, and `interpAt_keyBounded` bounds fresh hook results by those ambient keys
plus their existing inputs. Only seven source-construction clauses of
`KeyBounded` receive the default-empty ambient list; the other 29 clauses keep
their input bounds unchanged.

`EvaluatorMinted` gives the selected evaluator's returned-state/key and world
growth obligation. `evaluatePrim_minted_with_ambient` and the projection lemma
prove `evaluatorFor_minted`. The existing command/replay proof bodies are
generalized once as `_of_evaluator` theorems; their original names remain
empty-ambient/default-evaluator wrappers. `AnswersValid` follows the selected
evaluator along the actual public replay. `handles_minted` retains its public
judgment and tape premise, now through that generalized replay theorem.

The focused native integration, updated dependency-report modules and the full
D5 repaired-tree gate pass at the existing axiom ceiling. This handle invariant
is not the outstanding frame/term simulation.

The numeric-ID repair (E4-CHECK-CE-010) also excludes the interruptor of
`SyncOp.deferredInterruptWith` from the collected positions: it is written only
into Cause, which already excludes interruptor provenance, and is never used
to look up a fiber. The Deferred cell remains collected. The `KeyBounded`
record gains the `fiberIdValue` encoder bound alongside `fiberValue`; neither
the replay premise nor `handles_minted`'s conclusion changes.

Likewise interruptAll collects its target handles, but its optional numeric
interruptor is excluded provenance in both WithFiberAction and ActionName.
