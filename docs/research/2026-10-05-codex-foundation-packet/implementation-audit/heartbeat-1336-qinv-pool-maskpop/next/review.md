# CUTS and QINV: bounded source review

The review freezes main at `d4ea8243826e2d5e5b3750007df009d80c4b8741`.
It changes no repository file and runs no project command.
The finite controls execute a Python mirror of selected branches, not Lean or the repository model.

## Disposition

CUTS already adopts the earlier support in commit `357bebdd`.
Its brief retains the full run equality and derives replay laws through `tape_replays`.
The reviewed worktree is clean at `bc0ee4c19c833f751aec357558fe4620993b1059`, on `seat/cuts`.
No new connector or design note is present in that snapshot.
This records pending work, not failed acceptance.
No repeated CUTS advice is needed.

QINV is a brief awaiting a free seat at the frozen main commit.
Its assignment already permits a stronger invariant.
The following advice makes that permission concrete before dispatch.

## 1. Carry the current invariant, then reuse the existing closure laws

`FirstProfile` deliberately leaves the buffer free.
It does not imply `within`, `tidy`, or `quiet`.
`Run.ok` and `Run.named` are stored historical flags.
An arbitrary `Run` with true flags need not satisfy the current state properties.

The definitions are retained verbatim under `definitions/` and `source/`.
Their owners are `Effect4.Queue.Model` in these files:

- `src/Effect4/Laws/Modules/Queue/Model.lean`: `Run`, `within`, `tidy`, `quiet`, `accounted`, `bump`, and `step`.
- `src/Effect4/Laws/Modules/Queue/Profile.lean`: `FirstProfile`, `firstOp`, `Requested`, and `first_profile_closed`.
- `src/Effect4/Laws/Modules/Queue/Capacity.lean`: `positive_suspend_step_capacity`.

These finite witnesses use first-profile operations and satisfy `Requested`.
Unmentioned state fields have their declared defaults; old flags start true unless stated.

| Missing premise | State and operation | Result | Positive control |
| --- | --- | --- | --- |
| `within` | Capacity 1, messages `[7,8]`; `dropTake 99` | `ok` becomes false | Messages `[7]` |
| `tidy` | Capacity 2, no messages, pending single offer `(2,[8])`; `dropTake 99` | `ok` becomes false | Messages `[7,9]` fill the buffer |
| `quiet` | Capacity 1, message `[7]`, taker `(5,1,1)`, no signals; `poll` | Blocked poll leaves `ok` false | Signal history `[5]` |
| Old `ok` | Empty capacity-1 queue, old `ok = false`; `dropTake 99` | `ok` stays false | Old `ok = true` |
| Old `named` | Empty capacity-1 queue, old `named = false`; `dropTake 99` | `named` stays false | Old `named = true` |

All five witnesses and their positive controls pass in `witnesses.py`.
They identify missing premises; they do not prove the proposed invariant sufficient.

### Placement before the proposed statement

1. Concept: `reactive-scheduling`, preservation of an explicit state invariant.
2. Question: the model parts of proposed `wait-registration-no-gap` and `waiting-request-obligation-preserved`.
   Their full statements remain open parts, not existing proved claims.
3. Reach: `step .none`, positive-capacity suspend states, single offers and bounded-one takes, poll, and the two withdrawals.
   Keep `firstOp` and `Requested`; rows 219, 233, 255, and 275 bound this scope.
4. Exclusions: no program, typed cell, machine, signal delivery, fairness, liveness, or first-profile close/shutdown behavior.
5. Consumer: QINV's list-run law, then the Queue wrapper run law named in row 275, point 2; serving R12.

The smallest proposed statement is **UNCOMPILED**:

```lean
def FirstRunInv (r : Run) : Prop :=
  FirstProfile r.s ∧ within r.s = true ∧ tidy r.s = true ∧
  quiet r.s r.signalled = true ∧ r.ok = true ∧ r.named = true

theorem first_step_inv (r : Run) (op : Op)
    (h : FirstRunInv r)
    (first : firstOp op = true)
    (requested : Requested r.s op) :
    FirstRunInv (step .none r op)
```

Reuse `first_profile_closed` for the profile component.
Reuse `positive_suspend_step_capacity` for the capacity component.
Both currently expose the resulting state from a run with default history.
A small state-projection connector can transport them to an arbitrary `Run`.
Its candidate equality is `(step .none r op).s = (step .none { s := r.s } op).s`.
This helper serves the statement above; it is not another invariant proof.

For the remaining components, reuse `acceptLoop_single`, `wake_profile`, and `waiting_nodup` from `Profile.lean`.
Do not repeat the capacity proof or unfold pending-offer acceptance independently in each operation.
The list-run induction must require `Requested` at each current prefix state.
Checking every request only against the initial empty state is insufficient.
The candidate may need further invariant components; the brief explicitly permits that discovery.

## 2. Keep the fault controls outside the first-profile claim

`firstOp` refuses `close` and `shutdown`.
Those are the only `step` branches that inspect `Fault`.
Thus the existing faults cannot falsify the first-profile step statement.
They remain useful controls for the broader model.

The new packet retains two small controls with passing ordinary-step counterparts:

- Closing: capacity 2, message `[7]`, taker `(5,2,2)`, no signals.
  Closing lowers the readiness threshold.
  Dropping its signal makes `ok` false; the ordinary close leaves both flags true.
  The taker bounds also exclude this input from `FirstProfile`.
- Shutdown: capacity 1, message `[7]`, pending single offer `(2,[8])`.
  Dropping the shutdown signal makes `named` false; ordinary shutdown keeps both flags true.
  The initial state satisfies `FirstProfile`, but the operation is outside `firstOp`.

Name `Fault.none` as the positive control, rather than requiring it to be red.
Keep the broader fault controls separate from the first-profile theorem's red controls.
No domain expansion or model change is needed.

The exact existing exploration is `docs/research/2026-10-05-claude-lead/queue-contract/QueueLargeControls.lean`.
`Test/Program/QueueContract.lean` points there and excludes it from the default imports.
Add that path to QINV's reading list; do not rerun its large exploration for this review.

## Requirement accounting and evidence

All thirteen requirement titles and exact `openParts` lists match the previous `130639Z` packet.
Each list also matches the frozen registry and generated report.
The registry diff adds default module associations for `Laws.Modules.Waiting` and `Laws.Modules.Queue.Ops`.
It changes no open part.
The QINV and CUTS briefs propose work under existing questions; this review closes none.

`manifest.json` pins the source and prior evidence bytes.
`tool-evidence.json` retains explicit allocation, filing, and commit records with original line hashes.
`requirements.json` records the exact thirteen comparisons.
`witness-results.json` records every input and complete mirror result.
`receipt.json` records commands, scope, repairs to the scratch scripts, and verification.
