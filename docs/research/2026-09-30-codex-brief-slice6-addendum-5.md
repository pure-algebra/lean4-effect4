# Addendum 5 to the slice 6 brief: H2 part one, after Codex's audit of the probe plan

Written 2026-10-01 by the coordinator. Read it with the [brief](2026-09-30-codex-brief-slice6-and-fixes.md)
and addenda [1](2026-09-30-codex-brief-slice6-addendum-1.md), [2](2026-09-30-codex-brief-slice6-addendum-2.md),
[3](2026-09-30-codex-brief-slice6-addendum-3.md) and [4](2026-09-30-codex-brief-slice6-addendum-4.md);
where they differ, this one wins. The owner ruled on 2026-10-01, after reading Codex's
[audit](2026-09-30-codex-review-model-probe/audit.md) of the model probe's plan: "H2 part one go,
D1–D6 as amended."

**Amended by the owner on 2026-10-01, directly to Codex; see the end of this note.** Part one's
clause excludes `badName` and `notImplemented` only; `missingService` waits for row 117. Three
further rulings widen C's scope.

**The one thing first.** H2 part one is go, in addendum 4's order after H1: the eight named
existing-body repairs, the explicit clean-failure premise, the local exclusion lemmas, and nothing
more. H2 part two stays held: the audit's saved-frame counterexample makes it a design item (row
117), not a proof task. The six rulings D1–D6 are recorded as rows 111–116 and change nothing in
the current queue. The order stays: C step 5, D's held users, F, G, H1, then H2 part one.

**Checked by the coordinator.** The audit's four load-bearing probes (`SavedFrameTransport`,
`PackageAppend`, `DeadlockMutation`, `ClosedBeforeCleanup`) rerun in the main checkout at the
audit's base: exit 0, every printed theorem at `[propext, Quot.sound]` or less. The code facts
they rest on were read: `Module.rowDefs` puts a module's rows before its services' operations
(`Program/Authoring.lean:322-323`); `firstFreeName = 4` with the four machine keys below it
(`Machine/ContextMap.lean:787-790`); name safety stays in codegen by design
(`Program/Table.lean:11-13`); `HostSession.start` refuses a header whose table differs
(`Api/HostSession.lean:135`).

## Item A: ratified

A landed at `90df5d21` with the full regeneration, the eleven tests, twelve axiom prints, `dune
build` and `make check-ocaml`. Its regeneration moved the two closure manifests that addendum 4
permitted under F; the same permission covers A's change to `externalValue`'s closure. No other
generated path is permitted by this. `E4-HOST-CE-007` is REPAIRED; row 97's status is the
coordinator's.

## Item C: no change

Steps 3 and 4 landed (`be6631ab`, `e5cc184b`); step 5 is in progress. The brief's stop rules stand.
The merge into `refactor/phase1-phase3` follows step 5's regeneration and checks; this addendum
reaches the branch with that merge, and can be read from the main checkout until then.

## Item H2, part one: go

**The judgment.** `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex`, with exactly these
three arguments. `NoShapeDefect ty ex` is the exit lane's `badDefect` lifted
(`Test/Program/ExitTypeLane.lean:34-37`): it refuses `badName` and `notImplemented` always, and
`missingService` when `ty.requires` is empty. It reads the core `Defect` alphabet and
`ty.requires` only; no signature parameter, now or under rows 111–116 (the audit, §1: the
interface survives shape A).

**Where it goes,** as addendum 3 lists: `TypedProg`'s `pure` arm and every protocol post that
carries an exit; the saved-stack contracts (`Contracts.SavedOk`, `StackAccepts`); queued results
(`finish`, `observe`, through `preds.exit` and so `RCmdOk`); stored completions (`PromiseCell`,
the due list).

**What is authorized,** and the measured cost it answers (receipt, H2; audit §1, "eight remains
the original lower bound"):
1. The eight existing bodies, by name: Admission's `strongExit_success`, `strongExit_of_clean`,
   `cleanExit_of_never`; Residual's `strongExit_bool`, `settling_fork`, `strongExit_mono`; Stack's
   `strongExit_failure_of_error`, `popR_typed` (its two sites count once).
2. The explicit clean-failure premise on `strongExit_of_clean`: `cleanExit` alone permits
   `die badName`, so the strengthened statement takes `NoShapeDefect` as a premise and pairs it
   with `fitsExit_of_clean`. Say so in the docstring; do not claim `cleanExit` excludes the
   defects.
3. Local exclusion lemmas only, as the repair plan names them
   (`H2/mechanical/repair-plan.md`): a cause whose reasons are all interrupts, specialized through
   `InterruptProvenance`; exclusion under `stripFail` (`Cause.mem_stripFail`); under `combine`
   (`Cause.mem_combine`); under `sanitize`; optionally a success-and-weakening wrapper for
   `ExitOk`.
4. Membership's base `FitsExit` is unchanged. Part one does not touch `missingService` with a
   nonempty requirement row beyond what the clause states.

**The stop rule, measured not inferred.** If a ninth existing body fails after the eight are
repaired, stop, report the measured list with the compiler's attribution (the receipt's
`map_errors.py` route), and propose; do not repair it. Mechanical judgment substitutions and the
new helper declarations are not bodies. The audit's note that a different placement (failure
transport fields on the protocols, which would also repair `hookLaws_interpR`) may cost
differently is recorded, not chosen: land the measured placement.

**Controls,** as addendum 3 lists them:
- red: `strengthened_output_false` against the field-only placement;
- refused: current code that dies with `badName`;
- still admitted: a user `die`; `missingService` with a nonempty requirement row.

**Register.** Add `E4-TYPED-CE-007`, "a clause on finished fibers alone keeps shape defects out
of typed states", REPAIRED by part one. Update `E4-TYPED-CE-003`'s repair column. Then add
`E4-TYPED-CE-008` for part two (below), SEEDED, with the audit's probe as its witness.

**Receipt.** Per body: the statement change, the premise added, the lemma used. The axiom print
of every changed body and new helper. The ceilings before and after (M3bWorld, M6).

## Item H2, part two: held (row 117)

The audit proved (`2026-09-30-codex-review-model-probe/probes/SavedFrameTransport.lean`,
`AuditH2.loop_admitted`, `output_eq`, `output_bad`, at the ceiling) that the loop contract
accepts a saved frame from `⟨never, never, single nativeScopeKey⟩` to `EffTy.pure unit`: the
continuation condition is vacuous at answer `never`, the incoming `die missingService` satisfies
`ExitOk` inside, `popR` returns it unchanged, and it is excluded at the outer type. Iterator hooks
have the same error-column-only transport; the preempted-catch helper (`Stack.lean:163-165`)
sanitizes to an arbitrary destination type and keeps the defect; `.scoped` drops the requirement
in the checker (`Checker.lean:198-200`) while its residual certificate types the body at the
inner type. `preds.ServiceOk` is `ServicesFit w ctx.services` (`Assembly.lean:56`): present
services fit; it says nothing about presence, so the synthesis's route through row 51 and
`satisfies_iff_subset_keysRow` does not supply the missing premise.

Part two therefore needs a frame and operation contract amendment, with positive controls for
scoped and provision, before any proof is dispatched. That is row 117, the coordinator's. Codex
does not implement part two, and does not weaken the frozen stack theorem or add a reachability
premise to it. Propose the register line for `E4-TYPED-CE-008` in the receipt: "the frame
contracts transport `missingService` across a change in the requirement row", SEEDED by the
audit's probe.

## Rulings recorded, not for Codex now

Rows 111–116 record D1–D6 as the audit amends them: the signature parameter is Σ_app with the
core under DI-47 and extension conservative under C1–C8 as obligations (111); the typed state
reads the service table as a static world component, shape A (112); carriers per service code
(113); the three refusals at admission plus application-code consistency, with the lawfulness
evidence on `ProgramSource` (114); extension as a contract over the fully assembled table, with
programs and sessions pinned to their complete table and no append claim (115); the host-row
entry's domain bit (116). Row 21 is now "thread it". None of these changes A, C, D, F, G or H1.
They are the first slice of the M5–M7 brief, after G, with the audit's inventory (§3: 27 existing
sites, lawfulness on the source, the `*_map` premises, `initialWorld`'s non-default case, the
extension family selected from `R2Probe.lean`), measured by a fresh compilation first.

## Receipt and base

Same rules as addendum 4: narrow builds, commits by explicit paths, `LEAN_NUM_THREADS=1` for
regeneration, no push, no edits to `decisions.md`. Update the receipt in place: a new section
"After addendum 5" at the top with its one thing, the earlier sections kept below as history.

## Amendments by the owner, 2026-10-01 (ruled directly to Codex; recorded here by the coordinator)

1. **H2 part one's clause, corrected.** The "judgment" paragraph above wrote the full clause,
   `missingService` excluded when `ty.requires` is empty, while the part-two section held the
   contract that clause needs; Codex read the contradiction (receipt, "H2 — part-one exclusion
   clarified"). The owner: "two defects in part one; `missingService` waits." So part one keeps
   `ExitOk w ty ex` and the signature-free `NoShapeDefect ty ex` interface, but the clause ignores
   `ty` for now and excludes `badName` and `notImplemented` only. The conditional `missingService`
   clause is part two, with row 117's contract amendment. The eight-body cap, the clean-failure
   premise, the local lemmas, the controls and the no-ninth-repair rule are unchanged.
2. **C's reader checklist gains two handwritten OCaml files.** Step 5 found that the engine
   prelude (`ocaml/engine/tools/api_engine_prelude.ml`) still constructs the old fiber field and
   that both spawn substitutions advance fibers without a ledger append, and that the engine tests
   (`ocaml/engine/test/test_engine.ml`) read `.origin`. The owner: "finish C with this amendment."
   The prelude's load, make and spawn transcriptions append the exact `ForkRecord`; the four
   Fast/Ref provenance assertions inspect the machine ledger (a root has no record; a child keeps
   its parent, daemon flag and exact site). The extern map is unchanged.
3. **Two more generated manifests are permitted as C's producer outputs:**
   `ocaml/gen/closure-fibers_gen.tsv` and `ocaml/gen/closure-machine_gen.tsv`, the producer's own
   closure statistics for the changed record layout and spawn body. The owner: "include both
   generated manifests."
4. **One producer input changes:** `Effect4.Machine.ForkRecord` joins the engine entry's type
   roots in `ocaml/gen/roots.json`, because both spawn definitions are replaced by the prelude and
   the producer would otherwise emit a placeholder for the record. The owner: "include the
   ForkRecord type root."
