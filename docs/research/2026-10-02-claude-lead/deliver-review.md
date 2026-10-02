# `M6Ledger.step_deliver`: review, falsifier candidate, proof plan

Claude, 2026-10-02. Main pinned at `4c219956e9fa952a34bb37cb5f89ab0ce657f74c`; the working tree was
clean at that commit and was only read. No compiler, build, generator or edit was run. The
candidate (`candidate.lean`) is **entirely uncompiled**.

## The one thing to know first

The frozen goal is **false** at this base, and the candidate is a falsifier, not a proof.

`TypedProg` admits a raw scope-exit marker as *current code*. Its `scopeExit` constructor
(`Typed/Residual.lean:306`) needs only `ScopeLive`, the payload and a typed continuation, and
`ReadCode` reads current code through `TypedProg`. So a configuration where a running fiber's
current code is that marker, read by a queued `deliver`, is typed.

The machine never consumes the marker as a counted operation:

1. `prepareR` leaves it unchanged (`DenoteR.lean:65`).
2. `evaluateFiberR`'s `scopeExit` arm installs `.pure badShapeExit` (`EvaluateR.lean:184-187`). The
   source comment there says "outside that protocol".
3. `prepareScopedExitR` then finds no marker, and `settle` queues `loop`.

`badShapeExit = failure (die badName)` (`Denote.lean:44`), and `ExitOk`'s `NoShapeDefect`
(`Admission.lean:25-33`) refuses it at every world and type. So `ReadCode` fails after the step at
every later world: `output_refused`, then `step_deliver_false`.

Row 156 (the `E4-SCHED-CE-020` repair) does not close this. It covers only an *absent* scope. With
the scope present, the raw arm still installs `badShapeExit`. This defect has no register ID.

## 1. Goal, placement, consumers

- **Goal:** `theorem step_deliver (root : ProgramSource) (rootTy : EffTy) (id : FiberId)
  (yielding : Bool) : ProofGraph.Obligation (StepPreserves root rootTy (.deliver id yielding))`
  (`Typed/Assembly.lean:1760`; `#proof_wanted` at `:1924`).
- **`StepPreserves`:** `∀ w m rest, m.stuck = none → ConfigTyped root rootTy w m (cmd :: rest) →
  ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w' r.1 r.2`, where
  `r := driveStep (interpR root.program) m cmd rest` under `termEvaluatorFor root.program`.
- **Concept:** 4 (`reactive-scheduling`), operational preservation of the named configuration
  judgment `I` only. It does not cover progress, fairness, lowering or the host.
- **Consumers:** `stepKeeps_of_stepPreserves` (all eighteen) → `decisionKeeps_of_steps` →
  `typedState_reachable_of_steps` (`Typed/Edits.lean:433-446`) → `m7_of_ledger`.

## 2. The actual branch (`Machine/Fibers.lean:1861-1864`)

`deliver id` gives `settle id rest (evaluateR (interpRAt root m.completedExits) m f yielding)`.
This is **the whole term evaluator** on whatever code is current, not just a stack pop. `deliver`
is queued after an `answered` step (`sync`, a store op), and the continuation it then evaluates is
arbitrary code. So `step_deliver` is `step_loop`'s evaluation core without `runloopTop`,
`countOp` and `injectYield` (`Fibers.lean:1651-1656`).

`evaluateR` (`EvaluateR.lean:337-339`; `prepareIterR` `:329`, `prepareScopedExitR` `:309`) is `prepareIterR ∘ evaluateRawR ∘ prepareR`:

- **`.pure ex`** → `deliverR`. A success on a deferred interrupt becomes `.pure (failure
  pendingCause)`. Otherwise `popR` walks the stack and gives `continue_`, or `finished ex` (which
  queues `finish id ex` with the stack emptied).
- **`.vis (.inl op)`** → `syncOpStep`. Some result gives `answered` with `[.drainDue]` nested
  (queues `drainDue, deliver id`); none answers `unit`, also `answered`.
- **`.vis (.inr op)`** → `evaluateFiberR`, about 45 arms (§5). `scopeExit` is the falsifier arm.
- **`prepareIterR`** (not on `answered`/`commands`) → `prepareScopedExitR`. That closes a scope the
  marker names, or halts on `unknownScope`.
- **`settle`:** `continue_`→`loop`, `answered`→`deliver`, `parked` (with the deferred-interrupt
  split), `commands`, `finished`→`finish`, `stuck`→halt.

## 3. The falsifier (`candidate.lean`)

The witness mirrors M6Capstone's `H1HaltAmendment` (compiled), but with scope 0 present. That
store is `Test/Program/ExitConnector.lean`'s `scopeWorld`.

| Declaration | States |
| --- | --- |
| `badShapeExit_untyped` | `¬ ExitOk w ty badShapeExit`, at every world and type |
| `scopeStore`, `scopeStore_wf`, `live` | a store holding scope 0 is well formed; `ScopeLive world 0` |
| `valid`, `scheduler`, `observers`, `registration`, `typedState`, `machineTyped` | `J` holds at the single running root, whose current code is the marker |
| `marker_typed`, `root_saved` | `TypedProg.scopeExit` types the marker; `SavedOk` holds over the empty stack |
| `config` | `ConfigTyped … world machine [.deliver Api.root false]` |
| `result_queue`, `result_root` (`rfl`) | the step gives `[.loop Api.root false]` with the root's code `.pure badShapeExit` |
| `output_refused` | `∀ w, ¬ ConfigTyped … w result.1 result.2` |
| `step_deliver_false`, `step_deliver_universal_false` | `¬ StepPreserves … (.deliver Api.root false)`; the ledger's universal form is false |

The tactics are copied from the compiled precedents. The most likely repair points:

- the scope-store anonymous constructors (`⟨⟨trivial⟩⟩` for `ScopeEntryOk`/`ScopeOk`, as in
  `scopeStoreOk_addUnsafe`);
- `scopeStore_wf`'s `change`, with `by decide` on the `Decidable` instance as the fallback;
- the two `rfl` result lemmas, which run `evaluateR` in the kernel as `result_halted` does.

Expected axioms: `[propext, Quot.sound]`.

**Same arm, other goals (by reading, not checked):**
- `step_loop` fails on the same witness with `loop` queued, whenever `injectYield` returns `none`.
- So does the `evaluate` decision entry: `J`'s `LiveCode` admits an idle fiber on the marker, and
  `evaluate` queues `loop`.

## 4. Repair options (a decision for the owner or Codex; nothing weakened here)

The marker is produced in exactly one place: the `scoped` arm (`EvaluateR.lean:182`), inside the
guard's bind continuation, that is, the guard's `some ex` (run) position. `DenoteR` generates none.
It becomes current only through `popR`'s resume slot, and `prepareScopedExitR` consumes it inside
the same `evaluateR`.

- **R1 (recommended): `scopeExit` is a callback form.**
  - Remove the constructor from `TypedProg`.
  - Type the marker only where the machine consumes it: `TypedProg.guard`'s `run` premise and
    `FrameAccepts.resume`'s `run` premise, through a callback judgment (`TypedProg`, or the marker
    with `ScopeLive`, payload and continuation).
  - Add one lemma, `prepareScopedExitR_typed`, which turns a callback-current walk result into a
    `TypedProg`-current `SavedOk` after the close.
  - Current users of the constructor to move: `Typed/Seq.lean:62,177`, `Typed/Residual.lean:774,946`.
- **R2 (insufficient): forbid a raw marker head in `ReadCode`/`LiveCode`.** `TypedProg` still
  types `sync v` followed by the marker. A `loop` on it answers, queues `deliver` on the marker, and
  the falsifier moves to `step_loop`.
- **R3 (not allowed): change the machine's raw arm.** The machine is frozen, and rc.112 has no raw
  marker operation; the callback sits inside `onExit` (`internal/effect.ts:3938-3948`).

## 5. Proof plan once repaired (shared with `step_loop`)

The helpers below exist (✓) or are missing (✗).

- **`.pure` delivery.**
  - ✓ `popR_typed` (generic in the interpreter).
  - ✓ `walk_saved`, `walk_done`, `saveAnswerR_typed`.
  - ✓ `finish` payload and empty stack (row 134 (c)).
  - ✗ **G2: `HookLaws root (interpRAt root c) (frameProtocols root)`.** The evaluator runs
    `interpRAt root m.completedExits`. `frameProtocols`' iterator, loop and finalizer protocols are
    stated against `interpR`, which keeps each point's own completed view (`InterpR.lean:311-326`
    vs `:398-414`). The generator walk folds an awaited fiber's exit from that view
    (`inlineYield` → `Point.awaitExit`, `DenoteR.lean:495-517`), so the two walks can take
    different steps. `popR_typed_interpR` therefore does not apply.
    - Either restate the three protocols for every completed view typed at the world (`J` types
      every exited fiber's exit),
    - or prove a walk simulation under a larger typed view.
    - Not shown false; not derivable from the current definitions.
- **Deferred-interrupt delivery.** ✓ `strongExit_of_clean`, `InterruptProvenance`.
- **Store ops.**
  - ✓ `storeStep_typed`, `StoreImplements` (31/31), `storeStep_answers`.
  - ✓ `configTyped_frame`/`StoreFrame`, `Guard.syncOpStep_storeKeys`.
  - ✓ queued `drainDue` (`drainDue_preserves`).
  - ✗ one `StoreFrame` builder per row: the `loop` store arm of `note.md` §6.
- **Value-answer fiber arms** (`getId`, `getContext`, `setContext`, `ambientScope`, `sync`,
  `snapshotChildren`, `dropObservers`, `suspend`, `foreignRelease`, `closeWalk`, `frontier`,
  `interruptScoped` self).
  - ✓ `*_answers` (`Adequacy.lean:1213-1290`), `configTyped_rupdate_*`, `configTyped_cons_loop`.
  - ✗ one fiber-edit wrapper per arm.
- **Guard, mask, gen, loop, closeIter-seq.**
  - ✓ `TypedProg.guard_frame`, `mask_frame`, `gen_frame`, `loop_frame`, `closeIter_frame`,
    `saveAnswerR_typed`.
  - ✗ G2 again for `gen`/`loop` entry (`interpRAt.iterNext`/`loopEnter`).
- **Async park** (sleep, await, external).
  - ✓ `async_frame`, `asyncPre`.
  - ✓ `configTyped_rupdate_park` (landed with registration; its exclusion here is `keysBelow`, since
    the token is fresh at `nextToken`).
  - ✗ registration → timer/waiter transfers: `WorldValid.timers`/`.waiters` at the new key;
    `SleepDemand`/`AwaitDemand` from `asyncPre`.
- **Await/join, awaitAll(FailFast), awaitNewChildren** (`FiberAction.join`, `countdownPark`).
  - ✓ `awaitValue_frame`, `joinEffect_frame`, `awaitAll_frame`, `*_delivered`.
  - ✗ observer-add edits (stored `resumeAwait`/`countdown` keyed at fresh tokens), an immediate
    answer when the target has exited, and `CountdownPayload` construction.
- **Fork, forkIn, forkScoped, runIn.**
  - ✓ `fork_answers`, `forkIn_answers`, `forkScoped_answers`, `runIn_answers`.
  - ✓ row 134 (e) bounds; `ScopeLive` from `fiberPre`.
  - ✗ the spawn-at-`nextId` edit (shared with `launch`, which another seat owns) and the
    `link`-queue facts.
- **interrupt, interruptAs, interruptAll, cancelRace.**
  - ✓ `interrupt*_frame`, `cancelRace_frame`, `configTyped_interruptRecord`.
  - ✗ the queued `interruptTarget`/`afterInterrupt`/`raceCancel` head facts (`CommandDeliveryOk`).
- **raceAll** (`beginRace`). ✓ `raceAll_frame`. ✗ race creation with a fresh token
  (`RacePayload`, `raceObservers`), plus `[launch, registrationDone]` queue ownership.
- **raceRegister** (marker current; `ReadCode` exempts it).
  - ✓ `RegistrationState` gives the race.
  - ✗ `registerRace`'s queued pair. Its halt (`unknownRace`) is ruled out by `RegistrationState`.
- **closeScope, closeIter-par** (`closePar`). ✓ `closeScope_frame`, `closeScope_installs`,
  `closeWalk_typed`. ✗ the store edit and its queued daemons.
- **yieldNow.** ✓ `configTyped_postTask`, `yieldNow_frame`. ✗ the wrapper.
- **refuse.** `fiberPre … refuse = False`: unreachable from typed code.
- **`prepareScopedExitR`.** ✗ under R1, `prepareScopedExitR_typed`: `closeScopeUnsafeR` +
  `finalizerR` typing. The halt is ruled out by the callback's `ScopeLive`.

## 6. Evidence limits

- **Nothing is compiled.** The falsifier is one finite witness: a single fiber with no stack,
  scope 0 present, `deliver` queued.
- **What it refutes:** the frozen statement over all `ConfigTyped` inputs. It does not claim that a
  reachable state carries a raw marker at a command boundary. By reading, the `scoped` arm's
  marker is always consumed inside the same `evaluateR`; that is unproved.
- **G2 is a gap, not a refutation.**
- **Revision:** `4c219956e9fa952a34bb37cb5f89ab0ce657f74c`. Blob ids:
  - `Machine/Fibers.lean` `7d5f3ece`
  - `Laws/Program/EvaluateR.lean` `af48ff26`
  - `DenoteR.lean` `a6b68b9f`
  - `InterpR.lean` `3d70b1f7`
  - `Typed/Residual.lean` `089c543d`
  - `Typed/Admission.lean` `985f3d52`
  - `Typed/Assembly.lean` `fb65c5e0`
  - `Typed/Stack.lean` `4dd3f46b`
  - `Test/Counterexamples/Machine/Semantics/M6Capstone.lean` `ae5d3309`
- **Proposed register row:** `E4-TYPED-CE-0xx`, "`StepPreserves` for `deliver` is false: a typed
  raw scope-exit marker as current code becomes `badShapeExit`", with repair R1. Codex owns the
  register.
