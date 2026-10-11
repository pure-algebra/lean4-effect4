# Live command frame classification

The guarded native command now retains a live predecessor and a word without stack clearing.
The unconditional raw theorem projects the same command census.
The full mask-table connection, source birth provenance and run stack locality remain open.

## Base and scope

Base: `e105520a6` on `codex/last-planned-goals`.
The enclosing commit is this landing's head.

Concept: reactive-scheduling, serving R11 and the saved-mask region bracket.
Registry question: `saved-mask-region-bracket`, role preservation, at `Effect4.Program.compiled_region_bracket`.
The mask reader also serves `saved-mask-chain-runs` at `Effect4.Program.compiled_mask_chain_runs`.
Both pointers belong to `tools/ProofGraph/Registry.lean`.

The classification covers every native command at every interpreter, machine and pending list.
Its guarded form requires each `exitDone` target to have exited.
`guarded_driveStep_liveTransports` derives this condition from the existing `GuardQueue`.
The actual guard requires no new premise.

The result retains initialized fresh fibers and their later frame edits.
It does not identify their source points or establish their parent's context as the source.
It gives no progress, cleanup count, host agreement or stack boundary along a run.
A finishing frame move remains an explicit allowed move.
It differs from the command's unconditional `clearStack` edit.

## Changes

- `CommandFrames.lean` shares one native command census between the raw and guarded interfaces.
- `Transport.maskLater` derives the mask instance by induction over the clearing-free word.
- `Transports.liveOld` reads a live predecessor for an already allocated fiber.
- `MaskBracket.lean` connects the actual command authority to that classification.
- `Test/Program/CommandFrames.lean` reads the guard and refutes the unchecked raw-clear instance.
- `Test/All.lean` imports that reader and control.

The old command case proof is replaced, and its superseded update helpers are removed.
No second evaluator or command traversal remains.
`CommandFrames.lean` changes from 473 to 704 lines.
`MaskBracket.lean` changes from 311 to 328 lines.
These counts come from `wc -l` and `git show` at the base.
The additional lines state the live relation, composition, projection and guard boundary.

## Verification

`LEAN_NUM_THREADS=3 lake build Test.Program.CommandFrames Test.Machine.MaskBracket`

The narrow build passes with 875 jobs.
`C2LiveCommandsBuild.log` retains the exact output.
The raw-clear control proves that the stronger relation fails without command authority.
It uses an arbitrary machine, not an admitted run or an outside-runtime counterexample.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/C2LiveCommandsAudit.lean`

The audit checks 201 declarations within `[propext, Quot.sound]`.
It reports zero declarations modulo goals and zero planned goals.
`C2LiveCommandsAudit.out` retains the output.
The final module-header placement edit changes comments only; the consumer build checks that source afterward.
`git diff --check` passes.

## Gates and remaining work

This landing changes proofs and readers only.
The completed truth and host-protocol comparisons are retained in `history-behavior-sweep-receipt.md` beside this receipt.
No whole-tree battery, whole-tree axiom gate or policy check runs.

C2 still needs the complete allocation interval and source/parent context witness for new fibers.
The existing whole-machine `MaskAged` proof still supplies its shared birth table.
C1's polymorphic machine invariant cleanup remains open.
B3 still needs the run connection that discharges the region bracket's `inside` premise.
The scenario writer histories remain open in their own lanes.
