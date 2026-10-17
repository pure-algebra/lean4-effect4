# 2026-10-17 Math seat, D3 landing: receipt

Status: receipt (history, not authority). Seat: math and formalization, the one Lean seat.
Base: `719e039bf` on `refactor/phase1-phase3`. The branch was cut at `898a68380`, rebased onto
`09638d1fc`, then onto trunk after the scenario retirement (decisions rows 409 and 410). Head: the
commit that updates this receipt, on `seat/d3`, not pushed. The note is `docs/research/2026-10-17-d3/README.md`.

## Commits

| Commit | Slice |
| --- | --- |
| `36b88b06f` | (a) an undeclared nominal reference has no member |
| `7fe779cbb` | (b) the world's declaration table, and `Fits` as its least fixed point |
| `3ac3c27a3` | (d) the term typer's readers under the table, at membership |
| `16aa8ee1c` | (c) the premises go: the tie, a table within the world's, items 3 and 4, and the column checks |
| `74f9e08ad` | the semantics report after D3 (`make gen-semantics`) |

## Changed files

| Slice | Files | Main changes |
| --- | --- | --- |
| (a) | 6 | `Program/Typed.lean`, `Program/Columns.lean`, `Laws/Program/Admits.lean`, `Laws/Program/TyDecls.lean`, `Typed/Membership.lean`, `Typed/FitsIn.lean` |
| (b) | 32 | `Typed/World.lean`, `Typed/Validity.lean`, `Typed/Membership.lean` (`FitsAt`, `NameFits`, `Fits`), new `Typed/Declared.lean` and `Laws/Program/TyDeclsInhabited.lean`, `Typed/FitsIn.lean` removed, the typed denotation and command clauses at the tie, six batteries |
| (d) | 1 | `Typed/Declared.lean` |
| (c) | 49 | `Typed/Admission.lean` (`Tied`, `ProgramSource` without `untyped`), `Typed/Declared.lean` (`TyDecls.Within`), `Typed/RecordOperations.lean`, `Typed/Denotation.lean`, `Typed/Denotation/Terms.lean`, `Typed/ExitConnector.lean`, `Typed/AnswerSchema.lean`, `Api/HostSession.lean`, `Api/Live.lean`, `Run/CallTree.lean`, the Pool, Queue and Semaphore laws, `Program/Admission.lean`, `Program/Columns.lean`, twelve batteries |

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=2 lake build Effect4 Effect4.Laws`, at (b), (d) and (c) | `Build completed successfully (1371 jobs)` |
| the same build, at (a) | one proof broke (`obligations_expand`'s reference arm, `Laws/Program/TyExpand.lean`); (b) repairs it |
| `make batteries-touched BASE=898a68380`, at (b) | 57 batteries, green |
| `make batteries-touched BASE=7fe779cbb`, at (d) | 2 batteries, green |
| `make batteries-touched BASE=3ac3c27a3`, at (c) | 76 batteries, green |
| `#axiom_audit` over the changed library modules, at (b) | 4617 declarations within [propext, Quot.sound], 1 planned goal |
| `#axiom_audit Effect4.Laws.Program.Typed.Declared`, at (d) | 43 declarations within [propext, Quot.sound], 1 planned goal |
| `#axiom_audit` over the changed library modules, at (c) | 4694 declarations within [propext, Quot.sound], 0 planned goals |
| after the rebase onto `719e039bf`: `LEAN_NUM_THREADS=2 lake build Effect4 Effect4.Laws` | `Build completed successfully (1371 jobs)` |
| after the rebase: `make batteries-touched BASE=719e039bf` | 245 batteries, green |
| after the rebase: `make gen-semantics` | 3 planned goals, from 8; committed as `74f9e08ad` |
| `python3 scripts/check-language.py --strict` on the note and on this receipt | `PASS` |

No root build, no `lake build Test`, no `make check-*` target ran. The coordinator runs `check-ts`
and `check-ocaml`.

## Open obligations

1. DI-57: the frame machine converts an answer at the row table only. A value it refuses there is
   passed unchanged, so the typed state holds; a host handle at a declared column is not minted.
2. The OCaml engines' reply admission at the application's table, the coordinator's slice.
3. `fold_of` for `FitsAt`: bundle its three fixed parameters, or teach `fold_of` a fixed prefix.
4. `ListFoldRules` at a table: its fields quantify over every world, so
   `fold_typed_atomic_update` keeps `sig.types = []`.
5. The rebase onto trunk resolved three conflicts in scenario batteries that trunk deleted
   (`Test/Dogfood/Scenario/Routing/Calls.lean`, `Test/Dogfood/Scenario/Todo/Claims.lean`) or
   rewrote (`Test/Dogfood/Scenario/Routing.lean`): trunk's version stands. Only the head was built on
   the new base; the slices below it were built on the old one.

6. Slice (a) also made the column checks refuse a declared type before reading the table. Slice
   (c) repairs both checks (the note, §6); the touched batteries of (b) did not reach the two that
   show it.

## Bounded evidence

- The batteries ran are the touched ones; the whole battery set did not run.
- The OCaml and TypeScript faces were not run by this seat.
