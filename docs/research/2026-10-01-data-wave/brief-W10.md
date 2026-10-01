# Seat W10: the acceptance, p2's handler end to end (commit 10)

Written 2026-10-01 by the coordinator from probe R's text. Base: main after commits 5–9 merge;
named at dispatch. Read first: `README.md` here; synthesis §3.2 stage 1's acceptance
(`docs/research/2026-10-01-data-probe/synthesis.md`); probe R's note Q5 and its skeleton
`docs/research/2026-10-01-type-language-probe/R/probes/P2RecordHarness.lean` (compiles today with
six parts pinned by name), its host folder `R/host/p2/` (`printed-p2-records.ts`, the prelude
atoms, the two rows at p2's idiomatic object types with DB-15's `toPair`); the programs seat's
`ProbeTodayP2.lean` (`2026-10-01-data-probe/programs/`).

**The one thing.** This is the wave's v0 marker (the owner, 2026-10-01): p2's handler authored
through `Api.Author` with two host rows, checked at answer `Response`, run through the keyed
session against a scripted host answering rc.112's objects, printed and read back exactly, the
printed module passing tsgo 7 against p2's idiomatic signatures with DB-15's error adapter, and
the three answers equal to rc.112's. Bounded as the synthesis states: the handler only; errors as
DB-15's literal-tagged pairs; the id's text threaded by the caller (row 131); the decode in the
host (route A, `Boundary.adapt`); `CurrentUser` as a value (row 118). The layered program,
in-program decoding (row 123) and structured service carriers are not this commit.

## The work

1. Copy the skeleton into `Test/Program/P2Acceptance.lean` (reachable from `Test/All.lean` at the
   anchor after `Test.Program.H2PartOne`); fill `parts` with the landed definitions (`Ty.record`,
   the two term builders, `Schema.encode`/`decode` at records, `Boundary.adapt`); flip the pins:
   `acceptance = some expected` (the checked type `Response` with the infrastructure pair as error;
   the three answers `{"status":200,"body":"bob"}`, `{"status":404,"body":"no user 9"}`,
   `{"status":401,"body":"bad token"}` modulo key order; the printed module reads back as the built
   program; the adapter strips `createdAt` and the codec refuses it) and `printedText` equal to the
   target module of `R/host/p2/printed-p2-records.ts`.
2. Host check (`Test/...` battery plus the host lane's script): the printed module with the prelude
   atoms and the two rows passes `tsgo` 7 (exit 0; without the error adapter two TS2375; today's
   positional module twelve); run under bun against rc.112 for the three answers; log versions.
3. Then p1, p3 and p5 as far as their non-data needs allow (forms, cells, queue): each as a battery
   that pins exactly where it stops and why (the row that owns the gap: R4 record cells, row 123,
   Queue), so v1's list is measured.
4. Final: `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` green; `make check-truth` and
   `make check-target` green.

Rules: plan §4; one TypeScript compiler, tsgo 7; nothing pushed. Receipt `receipt-W10.md` here: the
one thing first; the three answers as run; the printed module's tsgo result; where p1, p3, p5 stop;
the STATE line "v0's acceptance program runs".
