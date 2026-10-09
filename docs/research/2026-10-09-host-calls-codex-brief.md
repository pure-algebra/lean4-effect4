# 2026-10-09 Brief for Codex: review and probe the host-call design and the trust repair

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that carries
this file. The note under review: `docs/research/2026-10-09-host-calls-and-cleanup.md`.

## 1. The one thing to know first

The owner asks for an adversarial review of that note, with probes. The note proposes one form
for a host call: the operation of the row table's operation signature (`RowsSig`), with every
other form a realization. Find where
the design breaks before any slice lands. Change no file under `src/` or `tools/`.

## 2. What to review and probe

1. **The trust repair** (section 3 of the note). Check that the fixed walk
   (`tools/ProofGraph/Axioms.lean`, `bd65164b`) equals a plain search on roots of your choice. Try
   mutual inductive types, nested inductive types and recursors. Confirm or refute the finding
   on Lean 4.33's `collectAxioms`, and draft the upstream report with the smallest probe.
2. **The await table** (section 6.3). Probe whether one record type can replace `Await`,
   `BoundCall`, `ReplySlot` and `RetiredCall` as what a caller reads, with no state lost. Name
   any field the session needs that the table lacks.
3. **H9, the host as a handler** (section 6.4). Probe its statement on the repository section of
   `Test/Api/SessionMeaning.lean`. Is the meaning under a handler the meaning under the tape the
   handler gives along the run? Name the premise on the handler that it needs.
4. **The immediate-answer lowering stage** (section 6.3). Probe whether an answer at registration and
   a park followed by its application give one observation, on one fiber.
5. **Preloaded answers** (cleanup C5). List every consumer of `ExternalStore.answers`, and what
   deleting it moves.
6. **Your open branches.** Say which hold work that the design should read first:
   `codex/host-lowering-plan`, `codex/data-codec-host`, `codex/tuple-ocaml` and the others that
   are not merged.

## 3. Cleanup of your worktrees

These five worktrees are merged into `refactor/phase1-phase3` and clean. Remove them, with their
merged branches, after you confirm that state again:

| Worktree | Branch |
| --- | --- |
| `module-design-review` | `codex/fragment-classification` |
| `module-semaphore` | `codex/authoring-branches` |
| `review-repairs` | `codex/review-repairs` |
| `run-replay-api` | `codex/run-replay-api` |
| `unguard` | `codex/unguard` |

## 4. The receipt

Write it under `docs/research/2026-10-09-host-calls-review/`. Give each finding an id, its
evidence kind, its probe and the smallest next action. Record the commands and their results.
Read axioms with the gate's walk (`exactAxioms`), not with `Lean.collectAxioms`.
