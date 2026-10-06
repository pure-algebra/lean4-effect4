# Next proof work after Queue

## Decision

The existing plan covers the next useful work. Finish its consumers before adding a broader proof programme.

This review ranks three items. The first two already have contracts and placements. The third is an existing planned goal.

No new semantic defect was found by this bounded source review. No theorem, compiler, runtime, generator or build ran.

## Scope and evidence

The source snapshot is main `0e6077b6`. The captured files and hashes are in `source-manifest.json`.

T5 `cb4ebce3` and later coordinator edits are outside this snapshot. The parent owns their review and current seat allocation.

`generated/semantics.md` supplies retained report evidence. Reading it does not rerun the proof graph or certify current build freshness.

The six Queue step statements are proved in the frozen source. Their observation is the reply, stored value and ordered notifications.

They establish no delivery, cancellation, liveness or public wrapper law. Their docstrings state these boundaries explicitly.

The five modifying-step typing goals remain planned at this snapshot. Their treatment is already coordinator work; this report adds no competing proposal.

## 1. Finish the saved-mask boundary chain

**Priority and status.** First prerequisite for the public Queue. Already specified in `briefs/seat-mask-brief.md`, with ratified design rows 244–246.

**Concept and placement.** The main behaviour claim is `saved-mask-restoration`: scope-lifetime-finalization, R11.

Its prerequisites are `saved-mask-image-membership` and `scoped-body-substitution-boundary`: store-typing and residual-program-typing, R4.

The face claim `mask-rows-table-premises` belongs to exact-codecs, R8. `mask-printed-form-profile` belongs to translation-simulation, R10/R11.

These are registry open parts, not existing proved declarations.

**Consumer.** The Queue wrapper masks registration and restores the caller’s saved choice around the wait.

**Hypotheses and observation.** Use both canonical saved images, a checked body at child 0, typed captures and the required later world.

Observe region entry, completed exit and the exact pending cause. A false saved choice leaves the executing fiber’s current flag unchanged.

Nested regions keep their own rules. Do not state that every step inside a body has the same flag.

The printed expansion has two extra entry checkpoints. Its client contract acquires and registers nothing before the body begins.

**Reuse.** Start with the existing membership machinery in `Laws/Program/Typed/Membership.lean`.

`fits_mono` requires `World.leHost`; `fits_hasTy` and `fits_live` have separate conclusions. Retain those premises and distinctions.

Reuse `pointTyped_child`, `interruptible_arm` and `uninterruptible_arm` in `Laws/Program/Typed/Denotation.lean` for the body connector.

`pointTyped_child` requires the exact node path, successful body check, typed environment and completed-exit membership.

Reuse `maskFrame` and `clause_mask` in `Laws/Program/Typed/Commands/Evaluate.lean` for typed-state preservation.

`clause_mask` proves `FiberClauseKeeps`; it does not already prove the five boundary behaviours.

Extend the existing `read_print` route with its lawful-spelling and readability premises. Do not add a second syntax relation.

**Positive and red candidates.** Reuse the brief’s nested-region and escaped-restore controls.

The sharp control applies a false saved choice under an interruptible fiber. The positive leaves that fiber interruptible.

A mutant that instead enters an uninterruptible region must differ. A pending-cause control must retain the complete cause at the restoring exit.

These are proposed acceptance uses of existing controls, not newly executed evidence.

**Exclusions and prerequisite.** No progress, target behaviour, Queue law or native-spelling equality follows from the boundary theorem.

The slice first fixes the exact saved-value encoding. It then states the placed goals before proving them.

Sources: `mask-second-note.md` F3, F6–F10; `seat-mask-brief.md`; the declarations named above; `SemanticsRegistry.lean` R4/R8/R10/R11 open parts.

## 2. Connect one Queue wrapper to its committed steps and notifications

**Priority and status.** Next after mask and the selected typing route. Already required by `waiting-design.md` F3/F5/F7/F8.

The contracts exist, but the frozen tree has no public wrapper theorem. This is an implementation obligation, not missing general planning.

**Concept and placement.** Use `queue-expansion-agrees` and `posted-wake-profile-agrees`: translation-simulation, R10.

The request obligation is `waiting-request-obligation-preserved`: reactive-scheduling, serving R10–R12.

Its required neighbours are `wait-registration-no-gap`, `posted-task-decision-preserves` and `posted-body-entry-typed`.

F7 names `embedded-budget-sufficient` as a contract obligation. The registry records the budget alternative within R12’s driver-continuation open part.

The slice must place its concrete budget goal there before proof work. The exact budget name is not a standalone registry claim today.

State the first concrete wrapper goal at those existing placements. Do not create a second Queue model.

**Consumer.** The first positive-capacity, open, suspend-strategy Queue with single-message take and offer.

**Hypotheses and observation.** Retain `FirstProfile`, `Requested`, the injective identity table, captured terms and actual step typing evidence.

The profile fixes take bounds at 1/1, singleton nonbatch offers, absent peekers and awaiters, and distinct request identities.

Observe public requests, commits, replies, interruption and termination before hiding the private cell or helper identities.

Keep each emitted notification occurrence represented until delivery or discharge. The current hint table alone cannot represent an older posted helper.

Before-consumption withdrawal consumes nothing. After-consumption interruption leaves the commit in place, even when no caller continuation runs.

A request pending under a mask is not a withdrawal. An old hint must be inert after the request rearms.

**Reuse.** `queue_steps_agree` supplies the six abstract-step connections.

`step_updates` joins the five mutations to `refStep_modify`. `cell_read` joins size to `refStep_get`; size stays a read.

`step_keeps_cell` uses `fold_typed_atomic_update` with explicit checker, environment, current-cell membership and successful-evaluation premises.

`Table.renew`, `Table.afterTake`, `Table.afterOffer` and `Notified` already own identity renewal and ordered emitted signals.

The wrapper adds occurrence ownership and scheduled delivery around these definitions. It must not rebuild their value-level proofs.

Use the existing fork, Deferred, mask and Run machinery. Keep the helper-per-signal profile and its declared dispatcher differences.

**Positive and red candidates.** Reuse the capacity-one workload, then supply actual posted helpers and waits.

Keep the uncancelled offer as a positive. Compare withdrawal before acceptance with interruption after acceptance and before the posted answer.

A mutant that erases an accepted message must fail the latter observation. A mutant that delivers an old hint into the new wait must fail rearming.

For the work limit, hold cell state and signal count fixed while growing the receiver continuation. Keep an empty continuation as the positive.

The bound must cover the reached drain, or the profile must refuse the longer client. This control is already specified in F7.

**Exclusions and prerequisite.** No infinite fairness, starvation result, general dispatcher resumption or whole-runtime agreement is requested.

`straight_sufficient` applies to `loadR e fuel` with `[evaluate, flush]`, plus depth and step bounds. It is not an embedded-dispatch bound.

A dispatch cut remains excluded until the existing driver can retain and resume its unfinished work.

The immediate prerequisites are the mask contract, the chosen typing evidence, and a concrete sufficient budget or admitted-client restriction.

Sources: `Laws/Modules/Queue/{Profile,Relation,Steps,Typing}.lean`; `waiting-design.md` F3/F5/F7/F8; `Laws/Program/RuntimeR.lean`; registry R7/R10/R11/R12.

## 3. Close one contained application proof: infrastructure failures escape

**Priority and status.** A useful independent proof after the Queue-critical work is staffed. This is an existing planned goal, not new scope.

**Concept and placement.** `Test.Dogfood.Scenario.Routing.infrastructure_escapes`, translation-simulation, R10. Its consumer is `Routing.routing`.

**Exact reach.** For every id, id text, tag, message and built program, successful authoring admission supplies the program.

The token is `secret`. The script is exactly `failing tag message`, at the scenario’s default budgets.

The tag differs from `NotFound` and `Unauthorized`. The root must fail with the same tagged payload.

This goal quantifies over values, but not arbitrary scripts. That makes it a more contained next proof than the other application goals.

**Reuse.** Retain `request`, `failing`, `opened` and `observe`. Prove the existing proposition in place.

`tagIs_pair` already supplies the exact failure-tag test. It alone does not prove handler routing on the machine.

Use the actual two-row table, session answer path and the existing Run driver for the short script.

`Scenario.tape_replays` can move its machine observation to raw replay after proving that the extracted tape has no remaining frontier.

That theorem retains the actual table and fuel. It proves machine equality, not session-ledger equality or an OCaml result.

Do not apply the empty-table agreement theorem to this host-row program. Do not infer machine behaviour from `meaning_catchCause` alone.

A helper should serve the fixed answer/handler segment that this goal consumes. Generalize only when a second real consumer needs it.

**Positive and red candidates.** Reuse the existing `SqlError`, `connection lost` escape control.

Reuse the existing catch-all mutant: it returns 401 instead of the unchanged infrastructure failure.

Retain the business-tag control outside the theorem’s premises. Its admitted broad error column intentionally routes that tag as a business failure.

**Exclusions and prerequisite.** No arbitrary-script noninterference, host execution, reply-admission theorem or unauthorized-call law follows.

The proof must establish the short script reaches its intended outcome with the stated budget. No new language construct is required.

Sources: `Test/Dogfood/Scenario/Routing.lean`; `Test/Dogfood/Scenario.lean` (`TapeReplays`, `tape_replays`); frozen `generated/semantics.md` R10.

## Why the other application goals rank later

`Workers.releases_once` covers every job count, budget and script. It states cleanup-log identity uniqueness, not eventual release.

`Timeout.stale_never_applies` combines retired-key exclusion, receipt uniqueness, application uniqueness and root-answer provenance across arbitrary scripts.

The existing `applied_guard_absent` establishes one applied guard’s absence. It does not supply that complete multi-step invariant.

Atomic’s four goals quantify over all scripts. Its duplicate-write control still does not replay one finalizer registration.

The HOST brief already supplies a measured host route and missing-observation policy. Treat it as planned acceptance work, not a new proof claim.

## Do not prioritize

- A generic algebra hierarchy. The scheduled list-lemma move and duplicate lookup-lemma retirement already address demonstrated reuse.
- A whole TypeScript or OCaml compiler theorem. Keep each reached primitive, table, numeric domain and observation explicit.
- A generic scheduler rewrite merely to prove the first Queue. Use the already-planned budget or client restriction if adequate.
- Infinite fairness, universal starvation freedom or arbitrary fair ticket composition. The first profile excludes those claims.
- STM, Semaphore, Pool or Cache implementation solely to enlarge the proof surface. Their design contracts can remain ahead of implementation.
- Whole-run exactly-once cleanup from local `close_twice` or log-count evidence. Those statements have different observations and premises.
- Reopening an old admission gap without reading the current `AdmittedSource` connection. The parent checks current admission evidence separately.
- A new proof-report framework. Existing goal placement, measured dependencies, axiom reports and scenario gates already serve these items.

## Review completion

All recommendations name an existing consumer and placement. Proposed controls remain unexecuted.

The source hash check rereads the frozen commit. It checks evidence integrity, not Lean validity.

No repository files, branches, active builds, seats or user drafts were changed.
