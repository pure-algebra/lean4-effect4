# Codex's packet for deeper proof support: the coordinator's filing note

Status: history, not authority. The owner asked Codex for deeper proof support and for a
watch on the proof graph. Codex wrote this packet at main `818a73ce`, and the owner pasted its
relay into the coordinator's session on 2026-10-06 (`relay.txt`). The coordinator filed the
packet's texts here, without its copies of tracked sources and without its larger result
files. `refs/candidate.lean.txt` is Codex's uncompiled sketch, renamed so that no tool reads
it as a source.

Do not run a script of this folder in place.

## What the coordinator did with it

- **The proof graph's repair is landed** (`27f6e5d6`). The coordinator read the patch
  (`graph/placement.patch`) and applied it unchanged. On the current report of 204 nodes the
  extended checker passes, and it keeps 60 explicit placements of nodes that no claim names.
  The coordinator measured Codex's count again: 27 placed nodes had neither a claim nor an
  entry of the population. A copy of the view without the new fallback fails the checker.
  `make gen-architecture` runs both checks. The drawing itself was not looked at.
- **The next proof slice has its place** (`c6e8ff05`). The semantics registry names the
  proposed helper claim `saved-mask-pop-discipline` among R11's open parts, with its
  consumers and with what it does not say. `semantic/candidate.md` holds the statements,
  which are not compiled.
- **Seat REFS needed no relay.** It proved the top theorem at the brief's bound on its own
  branch (`00a37ffc` on `seat/refs`), before this packet was read.

## The scope of the mask's pop discipline

The slice is free for Codex in a scope of its own, or for a seat of the coordinator when one
is free. Either way it has one owner at a time, and the coordinator merges it.

| Item | Allocation |
| --- | --- |
| Base | the head of `refactor/phase1-phase3` that holds this note, or a later one that the coordinator names |
| Branch | `codex/mask-pop-discipline`, in a worktree of its own |
| New files | `src/Effect4/Laws/Machine/MaskDiscipline.lean` and `Test/Machine/MaskDiscipline.lean` |
| Root anchors | `src/Effect4/Laws.lean`: after `import Effect4.Laws.Machine.LiveStack`. `Test/All.lean`: after `import Test.Machine.StoreKernelBank` |
| Not to edit | a file of seat PUB or of seat REFS; `src/Effect4/Machine/`; `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`, `generated/semantics.md` and `tools/Tools/SemanticsRegistry.lean` |
| Placement | `@[semantics "scope-lifetime-finalization" (requirement := R11)]` on the top theorem. The coordinator adds the registry claim at the merge, with that theorem as its pointer |
| One definition | the chain predicate of `semantic/candidate.md`. The filed probe's Boolean projection is a probe, and no second authority |
| Builds | every Lean and Lake command through `scratch/lean-slot.sh`, one module at a time. The coordinator runs the default build and the wide gates at the merge |
| Hand-back | a receipt in the handoff form of `AGENTS.md`: the statements as compiled, the controls with each red one red, the axioms, the narrow builds, and what stays open |

The slice ends at the local law and its adapter to `Machine.frameExitState`. The lift to runs
through `Machine.Lift`, with the pending commands' conditions, is a later slice. Its consumers
are the waiting wrapper under a masked caller and Semaphore's protected permit.
