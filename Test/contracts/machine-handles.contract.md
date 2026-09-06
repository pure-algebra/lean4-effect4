# Machine handle contract

Node: C13, `handles_minted`. Implementation: `src/Effect4/Machine/Handles.lean` (the
invariant at any name and thunk alphabet) and `src/Effect4/Program/Handles.lean` (the
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
   `compileEff_keys` (the compile names only the point's environment), `runStmts_keys`
   (the generator walker keeps to its environment), `actionAt_keys` (a `withFiber`
   action names only what its terms evaluate to) and `embed_keys` (embedded stores'
   programs carry the stores' keys).
4. Preservation is proved for every helper the command loop reaches: `spawn`, `start`,
   `injectYield`, `evaluatePrim` and each `withFiber` arm, `exitFiber` with its
   observers, `launchEntrant`, `linkScope`, `interruptRecord`, `settle`, `driveStep`,
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
  Deferred's waiter targets are excluded. The race's accepted exit and live entrants are
  collected because `fireObserver` passes both to `raceSettle`. Deferred waiter targets
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
