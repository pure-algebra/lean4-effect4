# Addendum 3 to the slice 6 brief: items G and H after Codex's side audit

Written 2026-09-30, after the owner relayed Codex's side audit of addendum 2. Read it with the
[brief](2026-09-30-codex-brief-slice6-and-fixes.md) and addenda
[1](2026-09-30-codex-brief-slice6-addendum-1.md) and
[2](2026-09-30-codex-brief-slice6-addendum-2.md); where they differ, this one wins.

**The audit.** It is copied, with its probes and logs, into
[`2026-09-30-side-audit/`](2026-09-30-side-audit/audit.md).
- **Rerun by the coordinator.** All six Lean probes ran against this checkout's built libraries:
  exit 0, every printed theorem within `[propext, Quot.sound]`, no `sorry`. The TypeScript probe's
  output is byte-identical to the audit's log.
- **Checked against the tree.** Each claim below was checked by the coordinator.

**The one thing first.** As addendum 2 wrote it, item H would restate M6 into two new false
statements:
- the queue fact has to type every queued command, not only resumes;
- "never goes wrong" has to live in the exit judgment that code, stacks and queued results all
  read, not only in the field for finished fibers.

Separately, item G must move two provision fixtures, or one regression goes on passing while
proving nothing. The order is unchanged: A, B, C, D, F, G, E, then H1 and H2.

## Item F: two green controls to add

Add the audit's controls (`2026-09-30-side-audit/probes/LayerControls.lean`) to F's counterexample
file. They check that the repair resets only the layer's own environment:
- `bodyRetainsOuter`: the program body under a layer keeps its outer variable;
- `serviceContextRetained`: the layer keeps the service context it requires.

Both hold for both local settings today, and they must still hold after F.

## Item G: move two provision fixtures

1. **The problem.** `leftWins` and `rightWins` (`Program/Provision.lean:607-608`) provide numbers
   under `dbKey`, whose service type is `handle "Db"` (`:472`).
   - G refuses both. They witness `E4-PROV-CE-002` ("a layer's signature determines the context
     it builds").
   - Their typing guard compares two checker results (`Provision.lean:610`;
     `Test/Program/ProvisionContract.lean:98`). After G it would pass as `none = none`, proving
     nothing.
   - The guards that build through `docsLayer` (`Provision.lean:611-612`,
     `ProvisionContract.lean:103-104`) would fail outright.
2. **The fix.**
   - Move both fixtures to the number-typed `dbBinding` (`Provision.lean:442`): `.merge (.succeed
     dbBinding (.nat 1)) (.succeed dbBinding (.nat 2))` and its mirror.
   - Assert that each types (`(layerTy docsSig leftWins).isSome`) as well as that the two types
     are equal.
   - Update the expected contexts: `buildServices` lists name 20, not 10, and the `getV` guards
     read `dbBinding`.
   - The audit checked that the new pair still builds two different contexts
     (`ProvisionProbe.lean`).
   - Update `E4-PROV-CE-002`'s register line to the moved fixtures.
3. **These two are expected and are not a stop under G's rule.** The coordinator found no other
   in-tree leaf that G changes. Every leaf is a number at a number key or a Boolean at a Boolean
   key in:
   - the OCaml goldens (`src/OCaml5/Eff/Goldens.lean:414-440`);
   - the typed corpus (`Test/Program/TypedCorpus.lean:66-76`);
   - the codegen tests (`Test/Codegen/ReadContract.lean:741-749`,
     `Test/Codegen/TemplatesContract.lean:28, 58`);
   - `Test/Program/CompileContract.lean:752, 768`.

   The audit's scan of the typed lane found no leaf at a key without a service type
   (`LayerControls.lean`, `missingServiceLeaves = []`).
4. **Controls.** Add the audit's two unknown-key programs to G's counterexample file:
   `untypedSucceed` and `untypedEffect` are well typed today and are refused with
   `serviceUnknown` after G.

## Item H1: the queue fact types every command and holds the guard's conditions (row 106, amended)

1. **The problem.** `QueueOk` (`Typed/Assembly.lean:87-90`) checks resumes and accepts every other
   command.
   - For the checked program `succeed(unit)`, the loaded state is typed (`loaded_typed`).
   - Yet a queue holding `finish root (success 42)` passes `QueueOk`, and running it gives the
     unit-typed root the exit 42.
   - So `M6Ledger.step_finish` is false (`step_finish_false`). So is addendum 2's token-strengthened
     `StepPreserves`, because the finish command carries no resume key
     (`proposed_step_finish_false`). Both are in `2026-09-30-side-audit/probes/TokenFinish.lean`.
2. **The payload part.** The queue fact applies the generated command check
   `RCmdOk (preds root) w` to every queued command. It is generated from the command residue rows
   (`Typed/Sources.lean:63-65`: `finish` and `observe` exits at the fiber's type, `resume` through
   `ResumeOk`). The probe proves it refuses the bad finish (`bad_generated_command_rejected`).
3. **The state part.** Mirror the guard's `GuardQueue` (`Laws/Program/Guard/Core.lean:1111-1116`)
   on the reference machine:
   - **authority** (`CommandAuthority`, `:1094-1104`):
     - `loop`, `deliver`, `finish`, `afterInterrupt`, `closeParAwait` and `raceCancel` need their
       fiber active;
     - `registrationDone`, `launch` and `enrollRace` need their race;
     - `exitDone` needs its fiber exited;
   - **owners:** unique;
   - **keys:** below `nextToken`, as addendum 2's freshness asks, and none of them the key of a
     parked external call (`ReservedKeys`);
   - **code sites.**

   The guard proves these for the same `driveStep` code on the native machine. Generalize what
   reads no code over the code type, as addendum 2 does for the key lists. For each command
   constructor, say in the receipt which condition excludes which bad instance. Name any you
   cannot settle.
4. **Pending tokens need no new bound.** `pending_below` proves it for every typed state, from
   `PendingOk` and `WorldValid.tokenBound` (`TokenFinish.lean`). Land it as a law. That closes
   addendum 2's open question.
5. **Controls,** in item B's `M6Capstone.lean`:
   - **Green.** `loaded_typed`, the tree's first typed loaded state for a program.
   - **Red.** `step_finish_false` and `proposed_step_finish_false`, against local copies of the
     old and addendum-2 statements.
   - **Refused.** The bad finish fails the new queue fact.
6. **Register.** Add `E4-SCHED-CE-017`, "M6's queue fact types every queued command", REPAIRED
   by H1.
7. **Proofs.** H1 changes statements only. The 18 command proofs are the M5–M7 brief's, against
   this statement.

## Item H2: "never goes wrong" lives in the exit judgment (row 107, amended)

1. **The problem.** Addendum 2 put the clause in the field for finished fibers only (`preds.exit`).
   - The code judgment's `pure` arm still accepts a defect exit: `strongExit_of_clean`, and under
     `Fits` the cause rule admits every defect (`fitsExit_of_clean`).
   - So a state whose current code is `pure (die badName)` satisfies the strengthened typed
     state, and one evaluation records the forbidden defect (`strengthened_input`,
     `strengthened_output_false`).
   - With H1's queue fact, the same shows one step earlier: `loop` emits a `finish` the fact
     refuses (`produced_queue_refused`).
   - All three are in `2026-09-30-side-audit/probes/BadDefectCurrent.lean`. The state is constructed, not
     reached, but M6 quantifies over every typed state.
2. **The fix.** Put the clause in the exit judgment every typed position reads, for example
   `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex`. It goes everywhere an exit is
   judged:
   - `TypedProg`'s `pure` arm and every protocol post that carries an exit;
   - saved stacks (`Contracts.SavedOk` and `StackAccepts`, which already take the exit judgment
     as a parameter);
   - queued results (`finish` and `observe`, through `preds.exit` and so `RCmdOk`);
   - stored completions (`PromiseCell`, and the due list in `PromiseTable`).

   Ordinary defects stay admitted (`E4-TYPED-CE-003`).
3. **Probe first, in two parts.**
   - **Part one: `badName` and `notImplemented`.** These do not depend on the type, so the clause
     carries across frames unchanged. Restate, and measure which slice-5 walk proofs break
     (`popR_typed`, the exit laws, `walk_saved`). Each break should need only local lemmas: a
     combined or annotated cause adds no new reasons.
   - **Part two: `missingService` with nothing required.** Whether it is allowed depends on the
     requirement row, which differs between an inner frame and the one outside it. Moving such an
     exit outward needs an argument that the service is present.
   - **If part two is not local,** land part one and report part two with its measured cost.
   - **If part one needs more than local edits** (as many as or more than `walk.diff`'s eight), stop
     H2 and report the measured cost.
4. **Controls:**
   - **Red.** `strengthened_output_false` against the field-only placement.
   - **Refused.** Current code that dies with `badName` is refused by the new judgment.
   - **Still admitted:**
     - a user `die`;
     - `missingService` when the requirement row is not empty.
5. **Register.** Add `E4-TYPED-CE-007`, "a clause on finished fibers alone keeps shape defects
   out of typed states", REPAIRED by H2. Update `E4-TYPED-CE-003`'s repair column.

## Not for Codex: numbers and the bridge

- **The numbers plan (row 108, not scheduled) gains two items** (`RefUpdates.lean`,
  `refusal-probe.ts`). The coordinator writes them into row 108 and `lcnf-route.md` §8.
  - **Store functions do arithmetic too** (`incr`, `double`, `takeAndBump`). Starting at
    2^53 − 1, two increments compare unequal in Lean and equal in the printed TypeScript.
  - **A refusal raised as a defect can be caught and hidden** (`catchCause`, `exit`).
- **A runtime-to-`Fits` bridge needs more than handle-freedom.** A context holding a string under
  a number key is handle-free and passes the shape check, yet fits nowhere
  (`ContextBridge.lean`). That is consistent with E keeping the runtime twin parked.
