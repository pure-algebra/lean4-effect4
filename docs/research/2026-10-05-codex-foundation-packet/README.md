# Codex's foundation packet of 2026-10-05 (a tracked copy)

Status: research note (history, not authority). Copied on 2026-10-05 at `0741ab17`.

**The one thing to know first.** These files are Codex's review packet for the transactions
note, the queues review and the groundwork plan. The owner ratified its recommendations on
2026-10-05, and Codex relayed that through `coordinator-note.txt`. Decisions rows 219 to 234
record the selections. This folder is the copy that those rows cite.

## What is here

| File | What it holds |
| --- | --- |
| `coordinator-note.txt` | The handover to the coordinator, with the owner's words as Codex relayed them |
| `contracts-and-literature.md` | The selections, the literature's consequences, the order and the stop conditions. It controls where `review.md` still describes a hold |
| `foundation-audit.md` | Five areas of the fiber and store foundations to strengthen, each with its placement |
| `review.md` | The option assessment, the evidence A to F, and the acceptance gates |
| `task/review.md` | The source review of posted programs |
| `literature/stm/contract-findings.md`, `literature/tasks/contracts.md`, `literature/scopes/review.md`, `literature/clocks/review.md` | The contract notes from primary sources, with proposed obligations |
| `atomic/cancel-return/` | The probe of cancellation after consumption, with its outputs on rc.112 and 4.0.1 |
| `atomic/inline-reentry.mjs`, `atomic/clock-profile.mjs` and their results | The inline reentry probe and the wall-clock probe |
| `model/` | The 22 checks of Codex's mirror of `TxModel.lean` |
| `scout/` | The probes of Effect 3's alternatives and of nested rollback, with their outputs |
| The `*.json` receipts and manifests | Inputs, commands, results, source hashes and download records |

## What was left out

- The downloaded papers, standards pages and their text extractions.
- The pinned third-party sources (GHC 9.12.2, Trio 0.30.0). The manifests keep their URLs and
  hashes.
- The packet's snapshot copies of this repository's own files.

The originals were under
`/private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review/`, which is a
temporary folder.

## What the coordinator checked

- The cancellation probe was written again and run on the default scheduler
  (`docs/research/2026-10-05-claude-lead/queue-probes/cancel-return.ts`). Its five controls agree
  with Codex's on rc.112 and 4.0.1. Effect 3.22.2 answers the same.
- The opposing-ticket cycle and the abandoned-ticket control are replayed in
  `docs/research/2026-10-05-claude-lead/tx-probes/TxModel.lean` (`opposingTickets`,
  `abandonedTicket`).
- The other probes and the literature were read and not run again.
