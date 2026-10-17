# 2026-10-17 Math seat, D3 landing: receipt

Status: receipt (history, not authority). Seat: math and formalization, the one Lean seat.
Base: `09638d1fc` on `wip/declared-ref` (the branch was cut at `898a68380` and rebased onto the
coordinator's head, which added only a report and a triage note). Head: the commit that adds this
receipt, on `seat/d3`, not pushed. The note is `docs/research/2026-10-17-d3/README.md`.

## Commits

| Commit | Slice |
| --- | --- |
| `9f03d2854` | (a) an undeclared nominal reference has no member |
| `703c41897` | (b) the world's declaration table, and `Fits` as its least fixed point |
| `9e5c9c577` | (d) the term typer's readers under the table, at membership |
| `ed11f238a` | (c) the premises go: the tie, a table within the world's, items 3 and 4, and the column checks |

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
| `make batteries-touched BASE=703c41897`, at (d) | 2 batteries, green |
| `make batteries-touched BASE=9e5c9c577`, at (c) | 76 batteries, green |
| `#axiom_audit` over the changed library modules, at (b) | 4617 declarations within [propext, Quot.sound], 1 planned goal |
| `#axiom_audit Effect4.Laws.Program.Typed.Declared`, at (d) | 43 declarations within [propext, Quot.sound], 1 planned goal |
| `#axiom_audit` over the changed library modules, at (c) | 4694 declarations within [propext, Quot.sound], 0 planned goals |
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
5. `generated/semantics.md` drifts: new placements (`fits_unfold`, `fits_memberIn`,
   `fits_iff_membersIn`, `evalTerm_progress` at R9) and five closed planned goals. Its producer is
   `make gen-semantics`, after a root build.

6. Slice (a) also made the column checks refuse a declared type before reading the table. Slice
   (c) repairs both checks (the note, §6); the touched batteries of (b) did not reach the two that
   show it.

## Bounded evidence

- The batteries ran are the touched ones; the whole battery set did not run.
- The OCaml and TypeScript faces were not run by this seat.
