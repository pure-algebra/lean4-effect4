# 2026-10-06 brief for seat TAPE: the tape's laws leave the test tree

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is the last slice of the close-out set (decisions rows 277 and 284, point 5). It
moves declarations. It changes no statement and adds no theory.

## The slice

Three claims of the semantics registry point into a test module: `run-tape-replay`,
`journal-position-replay` and `funded-run-replay`. Their theorems are general facts of a run
and of the runner's rows, and they name no scenario. They stand in
`Test/Dogfood/Scenario.lean` because the scenario driver was their first user. **Move them
into the library, beside `play_controls_eq_replay`** (`src/Effect4/Laws/Run.lean`), so that
the theory's claims point into the theory, and so that the inspection work of decisions row
281 has a library to call.

The list is seat WORKQ's receipt, item 11
(`docs/research/2026-10-06-seat-WORKQ-receipt.md`): the tape (`MachineView` and its two
readers, `Position`, `replyDecision`, `decisionOf`, `readsOn`, `tapeFrom`), `TapeReplays`
and `tape_replays` with their steps, the four equations of `tapeFrom`, seat CUTS's four laws
with their step, `openedOf`, `tapeOf`, `funded`, `funded_replays` and `atRest`. The item's
second table gives further candidates of the same kind: the laws that playing rows keeps a
run's name, budget and profile, and the inertness laws of a session and of a run's rows.
Move those too where they name no scenario. The item's third list says what stays.

## Read first

1. `AGENTS.md`, in full: the rule for a new core module (`module`, `public import`,
   `@[expose] public section`; decisions row 200), the two roots, and the library-root gate.
2. Seat WORKQ's receipt, item 11, whole, with its two notes for this slice.
3. `Test/Dogfood/Scenario.lean`, whole, and each file that imports it
   (`Test/Dogfood/Scenario/`, `harness/truth/session/Keyed.lean`).
4. `src/Effect4/Laws/Run.lean` and the modules under `src/Effect4/Run*`, for the homes.
5. Seat CUTS's receipt, proposal 5 (`docs/research/2026-10-06-seat-CUTS-receipt.md`).

## The assignment

1. **A short design note first** (`docs/research/2026-10-06-seat-TAPE-design.md`): each
   declaration with its new file and its new name. The rule: an executable definition that
   a tool may call goes to a core module, if its imports allow that the `Effect4` root
   reaches it; each theorem goes to the law graph. Name each definition that cannot be a
   core definition, with the import that bars it. Keep each declaration's short name. Say
   the namespace. Send the note's path and the table, and go on.
2. **Move, in one or two green steps.** The moved theorems keep their statements, up to the
   namespace of the names in them, and their `@[semantics]` tags. `Test/Dogfood/Scenario.lean`
   keeps the driver's alphabet, the record, the gate and the `note`, and it imports the new
   modules. Each battery of the scenarios passes with no change of a guard.
3. **Give the list of pointers** that the coordinator must change in the registry, and the
   anchors of the three dictionary entries that name a moved declaration ("journal's cut",
   "completed prefix", "stopped row" in `docs/core/controlled-english.md`). You may edit
   those three anchors, since `make check-language` reads them; change nothing else of that
   file.
4. **Stop rule.** If a declaration does not move without a change of its statement, leave it
   where it is and say why. A move that needs a new lemma is out of the slice.

**Not in this slice:** a new law; a change of `tapeFrom`'s meaning; a proof of a planned
goal; the session's verdict at a cut (decisions row 284, point 1, is the owner's).

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| Each moved theorem | unchanged: its tag moves with it | unchanged | unchanged | the scenario batteries; the registry's three claims; the prefix inspection of decisions row 281 |

## The files, and the rules

- New modules under `src/Effect4/` and `src/Effect4/Laws/`, as the design note places them.
  Root anchors: `src/Effect4.lean` and `src/Effect4/Laws.lean`, each after its last import
  of a `Run` module. Edit: `Test/Dogfood/Scenario.lean`, the files that import it,
  `docs/ARCHITECTURE.md` with `tools/Tools/ArchitectureRoles.lean` where a new module needs a
  row, `Test/Dogfood/README.md`, and the three dictionary anchors.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
  Until the coordinator changes the pointers, `make gen-semantics` is stale: do not run it.
- No file under `src/Effect4/Machine/` is edited. No generated fixture may move: run
  `make gen-fixtures` and read `git status`.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an
  error. No planned goal is added, and none is removed.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

1. For each moved theorem, the elaborated statement at the head equals the one at the base,
   up to the namespace: compare by `#check` in scratch, and file the comparison.
2. The default `lake build` passes, with the gate lines: the planned goals stay 28, and the
   count of declarations that rest on goals does not grow.
3. `make gen-fixtures` moves no file. `dune build` and `dune test --force engine` pass,
   through `opam exec --switch=effect4`. `make check-host-protocol` passes. `make check-docs`
   and `make check-language` pass.
4. Not run, and listed so: `check-gen`, `check-slow`, `check-corpus`, `check-target`,
   `check-truth`, the conservativity script, `gen-semantics`.

The receipt is `docs/research/2026-10-06-seat-TAPE-receipt.md`, in the handoff form of
`AGENTS.md`, one page: the one thing to know before merging; base, head and commits; the
table of each declaration's old and new name and file; the commands with results; the
pointers to change; what stayed, and why. One paragraph accounts for R1 to R14. Your last
message gives the head, the receipt's path and its first item.
