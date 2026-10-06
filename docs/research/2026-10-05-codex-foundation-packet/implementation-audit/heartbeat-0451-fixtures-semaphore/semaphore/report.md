# Semaphore card: guidance before freezing the draft

Status: source-only guidance on an active proposal. This is not a finding about landed implementation.

No native probe, Lean, compiler, build or generator ran. Source bytes and declaration anchors are retained in `hashes.json`.

## 1. The protected example does not always resume both waiters

The card’s section 9 says that releasing two permits resumes B, requesting two, and C, requesting one.

`callbackOptions` in pinned `internal/effect.ts` calls `fiber.evaluate(effect)` when an already-parked callback resumes.

`FiberImpl.evaluate` calls `runLoop` immediately. That loop can execute the retried acquisition and its continuation before the observer returns.

`SemaphoreImpl.releaseUnsafe` then checks the new free count before visiting the next observer.

Therefore, under no yield or interruption before B’s retry, B can take two permits inline. If B retains them, the walk stops before C.

Both recipients may resume on a different path, including one where B yields before its retry. That path needs its own explicit control.

**Smallest correction.** Replace the single expected trace with two named cases.

- No yield before B takes two; B keeps them. The walk does not visit C.
- B yields before retrying; C takes one. B later rechecks, cannot take two, and waits again.

The second case is the useful control for removing the retry check. The mutant must fail accounting on that specific path.

These are proposed source-grounded controls. Neither path was run by this monitor.

## 2. One atomic selection of the whole walk changes the policy

Section 4 proposes one `Ref.modify` for the walk’s selection. The selected source policy observes receiver changes between visits.

Selecting the entire eligible set from one cell snapshot can select B and C before B’s resumed acquisition changes free permits.

The card already marks callback reading as owed. Complete that reading before freezing the model or step statements.

**Smallest correction.** State one visit/eligibility transition, delivery, then the next visit against the resulting state.

The representation may use a cursor or another existing program construction. Its law must retain live insertion/deletion and receiver effects.

A preselected list is a different policy. It requires an explicitly named profile and cannot inherit native live-scan agreement automatically.

**Placement.** `semaphore-expansion-agrees`, translation-simulation R10, consumes this relation. Its notification clauses serve reactive-scheduling R12.

**Hypotheses and observation.** Name the admitted counts, actual callback state, scheduling decisions and sufficient work for the observed prefix.

Observe selection, attempted delivery, token acceptance, taken/free counts and body entry separately. Hidden wake order may still change visible commits.

**Reuse and exclusions.** Reuse the waiting-policy parameters from the factory plan. Do not infer public behaviour from Queue’s ordered signal-list relation.

This correction requests no fairness theorem, scheduler rewrite or universal work bound.

## 3. Qualify the protected finalizer law at execution frontiers

Sections 7 and 8 promise release at every exit. The intended boundary needs to distinguish a completed activation from unfinished cleanup work.

`onExitPrimitive` runs the pin’s synchronous release hook with its interruptibility-preserving third argument set to true.

The proposed `onExit` expansion runs a program finalizer, introducing work that may stop at a machine frontier.

A body exit alone does not establish that this expanded cleanup completed. `meaning_onExit` describes denotation; it does not supply the missing scheduled work budget.

**Smallest correction.** State at-most-once release per committed activation across every admitted prefix.

State exactly one release for an activation whose exit has completed through cleanup, under the declared sufficient-work or retained-frontier premises.

If cleanup has not completed, the activation’s release obligation remains represented. A frontier is not a completed exit or a typed failure.

Keep the immediate acquisition-to-hook installation protected. Keep the full delivered cause and caller’s saved interruptibility in the observation.

**Placement.** `semaphore-protected-permit`, scope-lifetime-finalization R11. Pool’s future lease is its second consumer.

**Positive/red control.** Cut immediately before and inside expanded release cleanup, then use the declared continuation or replay route.

The correct prefix retains the release obligation. A mutant that reports completion while discarding that obligation must fail the claimed observation.

This is the same work-limit discipline already stated by `waiting-design.md` F7. No whole-run liveness conclusion is added.

## Source anchors

- `waitForPermits`, `SemaphoreImpl.take`, `SemaphoreImpl.releaseUnsafe`, `SemaphoreImpl.withPermits`: pinned `Semaphore.ts`.
- `callbackOptions`, `FiberImpl.evaluate`, `FiberImpl.runLoop`, `onExitPrimitive`, `uninterruptibleMask`: pinned `internal/effect.ts`.
- `meaning_onExit`: `src/Effect4/Laws/Program/Denote.lean`.
- Card sections 1, 4, 7–9; factory plan waiting-policy section; waiting design F3/F7.
