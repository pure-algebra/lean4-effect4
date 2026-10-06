# Independent transaction boundary check

Restricting the existing `Eff` body and excluding host operations and ordinary Ref operations is necessary, but not sufficient by itself.
The roadmap should retain the existing ownership, call-closure, immutable-payload and budget premises.
No second transaction program representation is needed.

## Current authority

Source snapshot: HEAD `7e3f79111a021a65db2bb3288142db20b6130883`; exact inspected bytes are hashed separately.

- Decisions row 80 requires transitive non-reentrancy and an explicit ownership/replay or suspension contract before version erasure.
- Row 84 requires the embedded attempt's budget connector, including outer continuations and stores.
- Row 223 restricts `Eff` to pure terms, existing transactional cells, success, failure, retry and flat composition.
  It excludes allocation, in-body failure recovery, general loops and unresolved or reentrant calls.
  Commit bookkeeping finishes before receiver continuations run.
- Row 224 gives retry-only alternatives with selective rollback and dependency union.
  This is a later slice, not an implemented generic catch rule.
- Row 226 requires a sufficient embedded budget or a complete retained driver suspension.
  Restarting a fresh command with more fuel is not that suspension.

`docs/core/machine-state.md` §5 repeats these conditions.
Disabling automatic yield alone does not exclude inline receiver execution or calls through stored programs.

## What the target source actually provides

Both vendored versions' `Effect.tx` reuse an existing transaction context for flat nesting.
The outer call runs the supplied effect, then validates journal versions before commit or discard.
This validation placement is not itself a proof about every intermediate read of an aborted attempt.

Both versions' `TxRef.modify` call `f(current.value)` without cloning that value.
Their initial journal entry stores `self.value` directly.
Consequently, an unrestricted JavaScript callback can mutate a shared object before throwing or retrying.
Clearing the journal does not reconstruct that object's previous contents.
This is a source-level boundary argument, not an executed counterexample.

The admitted Lean pure-term route can avoid this behavior.
Its target relation must preserve immutable payloads or establish an equivalent ownership/copying discipline.
“No ordinary Ref operation” alone does not establish that relation.

Release 4.0.1 also changes two relevant details.
`awaitPendingTransaction` validates the read set immediately before waiter registration.
`commitTransaction` schedules wakes for written entries; rc.112 schedules them for every journal entry.
Thus the attempt agreement must name its version and exact notification observation.
Do not erase versions merely because a syntactic body filter passes.

## Existing placements and the smallest next obligations

The registry keeps the following as requirement open parts, not theorem declarations:

| Existing proposed claim | Placement | Immediate work |
| --- | --- | --- |
| `atomic-attempt-isolation` | `store-typing` and `reactive-scheduling`; R4 | State transitive admission and the single-owner invariant over ordered accesses, failure and retry. |
| `atomic-attempt-agreement` | `translation-simulation`; R10 | Relate the admitted attempt to the named release under isolation, immutable payloads and explicit retry. |
| `tx-choice-rollback-union` | `translation-simulation`; R10 | Follow the first transaction path; preserve enclosing writes and combine dependencies after double retry. |
| `driver-continuation-split`, `driver-suspension-keeps-typed` | `reactive-scheduling`; R12 | Implement retained suspension only if consumers need cuts; otherwise prove the embedded budget connector. |

`foundation-contracts.md` also places `embedded-budget-sufficient` and `wait-registration-no-gap` under R12.
The former includes any receiver code reached by delivery, unless the client profile restricts it.
The existing `fold-typed-atomic-update` theorem concerns one atomic Ref operation.
It does not supply a multi-cell transaction theorem.

The first admission proof should check every reachable call body, including stored-program and service calls.
A checked type signature does not establish the transaction profile.
Reuse the existing checker, stored syntax, world and driver relations for these obligations.

For an opacity claim, name the histories of live, aborted and successful attempts and their legal read observations.
State the serial reference relation and real-time constraint explicitly.
The isolated finite profile makes that route plausible; it does not make the theorem unnecessary.

## Proposed controls, not executed

1. A finite two-cell transfer supplies a positive case, including a failed attempt that restores the original cells.
2. An admitted-looking helper that calls a forbidden or reentrant operation tests transitive admission.
3. A one-step-short embedded budget tests refusal or retained ownership; it must not expose an intermediate attempt to another command.
4. An in-place array or record mutation inside an unrestricted target callback tests the immutable-payload boundary.
5. A stale read set before retry registration distinguishes the release's validation step from the pin's behavior.

These controls support the named claims; none was run in this source-only check.
There were no repository edits, builds, generators, compiler runs or runtime probes.
