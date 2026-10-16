# 2026-10-16 Math seat, second task: receipt

Status: receipt (history, not authority). Seat: math and formalization, the one Lean seat.
Base: `b3453c241` on `claude/math-d3` (itself on `81f9a4354`). Head: the commit that adds this
receipt, on `claude/math-d3`, not pushed. The note is
`docs/research/2026-10-16-math-graphs/README.md`.

## What landed

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Program/CallChain.lean` | new: call chains, three outcome judgments, refinement and `Chain.Equiv`, `RProgram`'s behaviour, `effChain`, `EffEquiv` |
| `src/Effect4/Laws/Run/Outcome.lean` | new: a driven session's outcome is its chain's; the planned goal `rows_divergence_adequate` |
| `src/Effect4/Laws/Run/CallMap.lean` | new: `request_performed`, every host request is performed at a site |
| `src/Effect4/Laws.lean` | three import lines, after `Typed.FitsIn` and after `Run.Journal` |
| `docs/research/2026-10-16-math-graphs/README.md` | new: the note |
| `docs/research/2026-10-16-seat-math2-receipt.md` | this receipt |

No file of the coordinator's D2 slice was edited. The new modules import `SessionMeaningLoop`,
`SessionRef` and `HeapSites` as they stand at the base.

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=2 lake build Effect4.Laws.Program.CallChain Effect4.Laws.Run.Outcome Effect4.Laws.Run.CallMap` | `Build completed successfully (564 jobs)`, warnings as errors |
| `#axiom_audit` over the three modules, in a scratch file importing `ProofGraph.AxiomAudit` | `64 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`; `6 … ; 1 planned goals`; `6 … ; 0 planned goals` |
| `python3 scripts/check-language.py --strict` on the note and on this receipt | `PASS` |

No root, no battery and no `make check-*` target ran, and `make batteries-touched` did not run.
The import lines in `src/Effect4/Laws.lean` are checked by no build of this seat.

## The proved laws

- `CallChain.lean`: `run_approx_none`; `Chain.finishes_le`, `Chain.waits_le`;
  `Chain.Finishes.not_diverges`, `Chain.Waits.not_diverges`, `Chain.Finishes.not_waits`,
  `Chain.Finishes.unique`; `Chain.Refines.diverges`, `Chain.Equiv.finishes_iff`, `waits_iff`,
  `diverges_iff`; `Chain.refines_of_sim`, `Chain.equiv_of_bisim`;
  `Chain.ofSystem_program_equiv`, `Chain.ofProgram_not_diverges`; `effChain_bind_succeed`;
  `EffEquiv.hostRunB_iff`.
- `Outcome.lean`: `runWith_finishes`, `runWith_exit_of_diverges`, `frontier_waits`,
  `frontier_of_diverges`, `effEquiv_runWith`.
- `CallMap.lean`: `request_performed`.

## Open obligations

1. The planned goal `rows_divergence_adequate` (R12). Its route needs the open claim
   `embedded-budget-sufficient`.
2. After D2, the session laws take `{app : SigApp}`; `Outcome.lean` and `CallMap.lean` follow.
3. `generated/semantics.md` will drift: one planned goal and new R6 and R12 nodes. Its producer is
   `make gen-semantics`, after a root build.
4. The proposed claims `call-chain-outcome`, `call-chain-equivalence`, `program-behaviour`,
   `rows-loop-outcome`, `rows-divergence-adequate` and `performed-rows`, if the coordinator takes
   them.
5. The note's §8: `Built.calls`, the dictionary row, the simulation of §3.4, a request-indexed
   protocol.
6. The coordinator's finding for the D3 landing is noted and not acted on. `Val.hasTy`, `Fits` and
   `FitsAt` read an undeclared `app n _` as a host handle: a duplicate arm since row 406.

## Bounded evidence

- The vessel reading is by source reading on `codex/vessel-dogfood`; no vessel run was made.
- The partner seat's Rocq files were read while in progress; its note was not yet written.
- The reach numbers of the note come from reading and name searches at the base.
