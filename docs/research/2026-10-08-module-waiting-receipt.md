# Waiting semantics preparation receipt

**The one thing to know before merging:** Cancellation settlement can resume another client before the canceled request finishes cleanup.
A shared waiting contract must retain module-owned resource settlement and delivery behavior.

## Base and head

Branch: `codex/module-waiting-probe`.
Base: `979be0ad8b86f356dc83aa7f6bdab46228684a32`.
Head: the commit containing this receipt, measured by the command below after the explicit-path commit.

```sh
git log -1 --format=%H -- docs/research/2026-10-08-module-waiting-receipt.md
```

Worktree: `/Users/pooks/.codex/worktrees/module-field-inference/lean4-effect4`.
The preserved branch is `codex/s1-load-review`, at `3b31c6c23059b1ed908a61ee667b53d30b2e8fd3`.
The initial worktree is clean before its branch switch.
This seat performs no primary-checkout build or edit.

## Changed files

| Path | Content |
| --- | --- |
| `docs/research/2026-10-08-module-waiting-semantics.md` | Source mapping, smallest shared interface, existing proof consumers, and proposed next obligations |
| `docs/research/2026-10-08-module-waiting-probe/host-controls.ts` | Positive host observations and deliberately wrong predictions |
| `docs/research/2026-10-08-module-waiting-probe/observations.json` | Retained runtime output |
| `docs/research/2026-10-08-module-waiting-probe/input-fingerprints.py` | Selected runtime fingerprints and vendor comparison |
| `docs/research/2026-10-08-module-waiting-probe/inputs.json` | Measured input identities and versions |
| `docs/research/2026-10-08-module-waiting-probe/run.sh` | Fingerprint, type, and retained-output checks |
| `docs/research/2026-10-08-module-waiting-probe/package.json` | Module format |
| `docs/research/2026-10-08-module-waiting-probe/tsconfig.json` | Strict tsgo configuration |
| `docs/research/2026-10-08-module-waiting-probe/README.md` | Replay command, control meanings, and limits |
| `docs/research/2026-10-08-module-waiting-receipt.md` | This receipt and the independent scalar review |

No production file, authority, root, generated file, or semantics registry changes.

## Commands and results

The final packet runs from the named worktree.

```sh
sh docs/research/2026-10-08-module-waiting-probe/run.sh
```

The command exits zero.
The runner reports its measured comparison result:

```json
{"positive": 11, "negative": 5, "retained_output_matches": true}
```

`inputs.json` measures Effect 4.0.1, Bun 1.4.2, and tsgo `Version 7.0.0-dev.20260629.1`.
It identifies selected inputs, rather than the full imported package graph.
The source-pair comparison checks installed source bytes against the vendored Effect 4.0.1 snapshot.
The compiler checks the probe strictly and skips dependency declaration interiors.

The initial check incorrectly reads an exit from `Fiber.interrupt`, which returns no value.
The repaired control polls the interrupted fiber after interruption completes.
Both final runtime and compiler checks pass.
No sleeps, scheduler replacements, installs, Lean builds, or whole-library sweeps run.

```sh
python3 scripts/check-language.py --strict docs/research/2026-10-08-module-waiting-semantics.md docs/research/2026-10-08-module-waiting-probe/README.md docs/research/2026-10-08-module-waiting-receipt.md
git diff --check
git diff --cached --check
```

The final language and diff checks pass.
The staged path check finds only the research files listed above.

## Axiom output

No Lean declaration lands in this packet.
This seat runs no Lean axiom check and claims no new checked theorem.

## Additional evidence

| Control | Actual observation | Consequence for the proposed interface |
| --- | --- | --- |
| Cancellation refund serves another partition | Successor B acquires before canceled A's outer exit cleanup; availability remains zero | Cleanup must run allocation and source-defined delivery, rather than only credit availability |
| Successor returns its reservation | B returns one permit; the original holder returns the other | Cancellation transfers reservation ownership to the successor in this checked run |
| Queue partial producer cancellation | Accepted 20 remains beside original 10; pending 30 disappears | A generic refund or rollback of all partial work would remove a committed message |

Evidence status: finite host controls checked.
Proof role: independent controls of a proposed shared waiting contract.
Scope: retained natural inputs under the installed default scheduler.
The batch Queue control reaches latest (Effect 4.0.1) and its richer batch profile.
The production wrapper exposes only the single-message offer.

This extends the earlier packet's separate solo refund and reentrant public-release controls.
It does not reproduce cancellation after selection deterministically.
It establishes no general settlement theorem, whole-module simulation, fairness, or liveness.

## Independent review of the scalar production slice

Reviewed worktree: `/Users/pooks/.codex/worktrees/module-folds/lean4-effect4`.
Reviewed head: `a6d3199e8e7152434cc781911fba1ffd2bb891c5`.
The tree is clean at review.
The production commit is `93f3fd435aa9fcaf0c9698855aae75fb42f6a949`.

The review reads these production files:

- `src/Effect4/Library/PartitionedSemaphore/Model.lean`
- `src/Effect4/Library/PartitionedSemaphore/Cell.lean`
- `src/Effect4/Library/PartitionedSemaphore/Data.lean`
- `src/Effect4/Library/PartitionedSemaphore/Steps.lean`
- `src/Effect4/Laws/Library/PartitionedSemaphore/Data.lean`
- `src/Effect4/Laws/Library/PartitionedSemaphore/Steps.lean`

No concrete defect appears in this scoped source review.
The independent model imports no Step implementation or Laws.
Its natural scalar rules match the inspected vendor branches.
`Model.reserve_eval`, `Model.reserve_reads`, and `Model.bookkeeping_agrees` retain both reservation branch premises.
`Model.bookkeeping_agrees` observes four source readings, rather than claiming a module run.
The connectors consume `Step.sound` and `Step.typed_of_normal` with the existing derived images and named contexts.
The core files do not import Laws.
The public builders reuse the existing step terms.

Evidence status: independent source review.
The implementation seat's receipt reports narrow builds and a scoped compiled axiom check.
This seat reads that audit and receipt but performs no build in the reviewed worktree.
Root integration still owes reachability, the semantics registry join, and concrete machine and emitted-program controls.
The scalar result does not establish waiting, cancellation, delivery, or client observation.

## Open obligations and next contract

Keep `Waiter.attempt` and `Waiter.withdraw` as the smallest shared program interface.
Semaphore, Queue, and Pool are actual consumers.
Keep retry notifications separate from decided answers.
Keep cancellation ownership and delivery behavior as module parameters.

The semantics note supplies the five placement fields for the next behavior obligations.
The existing `waiting-wrapper-typed` claim proves typing under its premises.
The broader waiting, cancellation, delivery, and protected-resource behavior clauses remain proposed open parts.
The next production slice must state those questions before proving them.

G1 still owns settlement and delivery.
G5 still owns the client program's observation.
G9 still owns contextual request identity correspondence.
G10 still owns observations across schedules and progress premises.
The host boundary stays with `docs/core/host-boundary.md`, and row 333 requires reply-admitted tapes.

Broader API and proof-graph organization proposals remain with the coordinator and the organizational seat.
No decision row, merge, or push belongs to this packet.
