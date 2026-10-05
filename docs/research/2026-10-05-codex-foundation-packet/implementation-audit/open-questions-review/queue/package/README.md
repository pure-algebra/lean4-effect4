# Queue Q0 integration packet

Status: prepared in scratch only.
The extraction and provenance checks pass.
No Lean source in this packet has been compiled here.
No repository, worktree, branch, build or generator was changed.

## What is prepared

| Packet file | Proposed destination | State |
| --- | --- | --- |
| `Test/Program/QueueModel.lean` | Same relative path | Exact extracted model definitions, with no evaluation commands |
| `Test/Program/QueueContract.lean` | Same relative path | Exact small named controls |
| `Test/contracts/queue.contract.md` | Same relative path | Reviewable abstract contract and proof placement |
| `retained/QueueLargeControls.lean` | A tracked research path chosen by the coordinator | Exact million-element regressions and bounded exploration; no default Test import |
| `candidates/QueueCapacity.lean.candidate` | None until checked | Complete helper proof draft and one permitted planned goal; uncompiled and excluded |
| `source/QueueContract.lean` | Retained packet evidence only | Exact source snapshot from `da41297b` |
| `extract_verify.py`, `provenance.json`, `verification.json` | Retained packet evidence only | Reproduction and hashes |
| `capacity_mirror.py`, `capacity-mirror.json` | Retained packet evidence only | Independent finite mirror, six named controls, 3,744 grid cases and one rejected mutation |

The model namespace remains `QueueContract`.
The extraction changes no definition body.
It moves evaluation commands into controls and leaves them out of the model module.
There are 51 retained `#guard` commands and six retained `#eval` commands across the split.
These are source-command counts, not counts of tests run by Codex.

The capacity candidate follows structural induction on pending offers.
It uses the standard list-length bound and arithmetic over the remaining room.
Its syntax and proof elaboration remain unverified.
Its planned step goal stays open even if the helper later compiles.

The independent Python mirror satisfies the bound on six named cases and 3,744 grid cases.
It rejects the deliberate variant that appends despite zero room.
This finite check does not validate Lean elaboration or establish agreement between the source and the mirror.

## Verify this packet

Run this command from any directory:

```sh
python3 /private/tmp/codex-effect4-overnight-monitor/2026-10-05-open-questions-review/queue/package/extract_verify.py --verify
python3 /private/tmp/codex-effect4-overnight-monitor/2026-10-05-open-questions-review/queue/package/capacity_mirror.py
```

The script checks exact bytes, coverage of every source fragment and preservation of all evaluation commands.
It also rejects a mutated model body and missing controls.
It invokes no Lean tool and writes only its receipt beside the script.

## Integration allowlist and ownership

The initial allowlist contains only the three proposed Test files above and a coordinator-named research receipt.
No file under `src/`, `generated/`, `ocaml/`, `tools/` or a live seat's worktree is in that allowlist.
The large-control destination is added only when the coordinator names it.
The proof candidate is added only after a later slot checks it.

The coordinator owns the `Test/All.lean` import anchor.
It must reach the new Test modules before the library closure gate runs.
The coordinator also owns any registry join and the final base and branch assignment.
Do not edit the registry's top claim to say Queue agreement is proved.

Two implementation seats remain active.
Do not open a third seat or compete for their build work.
Assign the eventual narrow checks through `scratch/lean-slot.sh` after a current seat releases its slot.
Use the coordinator's current toolchain and warning settings.

## Later acceptance, not executed here

1. Confirm the assigned base still has the same ruled model or review its exact changes.
2. Copy the allowed files into the assigned isolated branch.
3. Add the coordinator's Test import at its named anchor.
4. Compile the model and small controls through the assigned Lean slot.
5. Check the candidate separately before giving it a `.lean` destination.
6. Retain its actual plan status and axiom output.
7. Resolve any source or proof errors before accepting the slice.
8. Keep public Queue work after FOLD, T5 and the mask.

The packet accelerates abstract proof work.
It does not implement the effectful Queue, delivery wrapper, public API or target agreement.
