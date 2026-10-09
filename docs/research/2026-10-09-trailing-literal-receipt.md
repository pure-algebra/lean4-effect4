# A row's trailing argument is a name or a string literal — receipt, 2026-10-09

Branch `claude/jovial-wing-5c36ae`, worktree `.claude/worktrees/jovial-wing-5c36ae`.
Written at base `4a596d5b` (committed there as `9dffac12`), then rebased onto
`refactor/phase1-phase3` at `88d4a1f5`. Two commits on `88d4a1f5`:

1. `Rows: a trailing argument is a name or a string literal (RowArg)` — the change and this
   receipt. Ten files overlapped the new upstream commits: `ClassTable.lean` resolved by keeping
   upstream's taken names and reading `RowArg.names`; `profile.gen.ts` taken from upstream and
   re-cut; the rest merged cleanly.
2. `Repair the pins that the ifCase printing left stale` — `Test/Program/PoolFaces.lean` (two
   faces) and `generated/corpus-index.tsv` (41 rows, `chars` alone, +2 each). Merge `3fa881d2`
   repaired `QueueFaces` and `SemaphoreFaces` for `ifCase` but not these, so `Test` was red at
   `88d4a1f5` before this change. Separate so that it can be taken or dropped alone.

`refactor/phase1-phase3` has since moved to `78f7bcbe` (two view commits); they touch none of
these files.

## The defect and its cause

`Row.trailing : List String` was documented "names, never values", but the row of
`NativeOp.scopeMake .parallel` held the value `"\"parallel\""`, and `printRow` wrote every entry
as `Expr.ident`. The bytes `Scope.make("parallel")` were right; the tree held an identifier whose
text carries quotes, `SourceBindings` refused it, and `admitModule` refused pScope's module
(`refused: unbound`). The TypeScript reader carried the same workaround (`namesOf` matched a
parsed string literal by its quoted text).

## The change

- `Effect4.Program.RowArg` (`Program/Eff.lean`): `name (spelling)` | `str (value)`;
  `Row.trailing : List RowArg`; `RowArg.names` (the names alone). The parallel scope row is
  `[.str "parallel"]`.
- Printer (`Codegen/PrintLeaf.lean`, `PrintEliminators.lean`): `RowArg.print` writes `.ident` and
  `.str`. `rowNamesSafe` and `ClassTable.takenNames` read `RowArg.names`. `Row.printsRequest`.
- Reader (`Codegen/Read.lean`): `rowArgs?` (was `idents?`) and `Terms.rowArgs?` (was
  `Terms.names?`) read an identifier as a name and a string literal as itself; `spell` takes
  `List RowArg`; `noRow` sees literal arguments too.
- The reader's laws. `s("v")` is both the call of a row whose request prints as `"v"` and the
  call of a row whose trailing arguments begin with the literal `"v"`, so the table must exclude
  the pair. New field `LawfulSpelling.literal_alone`: under the spelling of a row of the domain
  that prints its request, no key begins with a string literal. Decided for supplied tables by
  `literalsAlone (nativeRows table)` in `LawfulTable`. The method view (`methodSignature`) cannot
  keep it (every non-method row prints a request there), so the old fields are now `LawfulKeys`,
  which `methodLawful` keeps, and `LawfulSpelling extends LawfulKeys`; the method readings take
  the premise `LiteralClear` from the signature itself. `nativeLawful` proves the field from the
  table check (`nativeSpell_mem`, `nativeRows_rep_of_dom`). `DefsNamed.unspelled` now covers every
  key of a definition's name (its docstring already said "spelled by no row"), which gives
  `LawfulSpelling.withDefs` its field.
- Registers: `tools/Effect4Gen/manifest.json` and `wire-tags.json` (`RowArg`: name 0, str 1),
  `tools/Tools/ProgramStructure.lean`, `src/OCaml5/Tools/EffGen.lean` (no corpus coverage for
  `RowArg`), `tools/Conform/Effect4/cases-policy.json` (`Terms.rowArgs?` renamed; a new default
  site `Row.printsRequest`), the proof-style baseline (re-recorded; entries only left).
- Engine mirror: the LCNF cut declares `row_arg = Placeholder_row_arg` (nothing in the engine
  reads a trailing argument). `scripts/lib/program_structure.py` now records such a family as an
  opaque boundary and keeps its declaration in `PROGRAM_TYPES`; the scenario test's checked row
  conversion refuses a row with trailing arguments rather than invent a value.
- TS: `ts/eff/read.ts` (`rowArgOf`, `sameRowArg`), `ingest/oxc.ts`, `ingest/ck.ts`,
  `ingest/render-readme.ts`.
- Batteries: `PrintContract` pins `Scope.make("parallel")` and its `.str` node; `ReadContract`
  reads a parsed `Scope.make("parallel")` (a `.str` node) to the parallel scope and refuses the
  quoted identifier; fixture spells and laws retyped in `ReadContract`, `TermRows`,
  `PrintTyped`, `RecordTerms`, `HostSessionContract`, `InvocationContract`.

## Commands and results, at the rebased head (both commits)

| Command | Result |
| --- | --- |
| `lake env lean --run tools/Drivers/Emit.lean <scratch>/emit-out` (the owner's probe) | 8 programs; README row `pScope … yes`, all eight rows `yes`; `pScope.ts` imports `{ Effect, Scope } from "effect"` and holds `Scope.make("parallel")`. At `4a596d5b` a scratch probe of the same core calls gave pScope `refused: unbound` before the change |
| `scratch/lean-slot.sh lake build Effect4 Effect4Laws Test OCaml5 Tools` | green, 1702 jobs; axiom gate: 1003 modules, 105315 declarations at `[propext, Quot.sound]`, exact boundary unchanged; goal gate: 31 planned goals, 14 declarations rest on them (as at base) |
| `#print axioms` of the new reader declarations (scratch, at `4a596d5b`) | none reaches `Classical.choice` or `sorryAx` |
| `python3 scripts/generate.py --only derived`, then `lcnf eff wire ts readme cas fixtures` | all PASS; derived, lcnf, eff, wire and ts bytes committed; readme, cas and fixtures unchanged; `TyView.lean` left at HEAD (below) |
| `make corpus` recipe (by hand) | 408 kept, 385 readable; at `4a596d5b` the index was byte-identical; at `88d4a1f5` 41 rows move in `chars` alone (commit 2) |
| `cd ts/eff && bun run typecheck && bun test` | clean; 761 pass, 0 fail |
| `dune build`; `dune test --force eff gen clock engine`; `ocaml/engine/tools/gen-check.sh` | all pass: prop_wire 6345 checks over random `RowArg`s, test_eff 691, test_lean_wire 121, metadata 207, engine differential 332 cases, queue/pool/semaphore/mask lanes; gen-check PASS |
| `python3 scripts/check-conform.py cases` | PASS, 242/242 |
| `bash scripts/check-conservativity.sh 88d4a1f5` | C1 PASS (385 retained byte vectors identical), C4 PASS (the two constructors named), C2 and C3 REFUSE (below); the corpus-index rows are reported as length-only; `--self-test` 27/27 |
| pScope pins against `harness/truth/corpus.json` and `generated/pScope.ts` (scratch render, at `4a596d5b`) | `expr`, `decl` and the module's `main` line equal the current printer's bytes |

## Open, bounded, host-only

- **Review event (owner).** This is no alphabet append: the row's encoding changes wherever a
  trailing list is not empty. No retained vector holds one, but `check-conservativity` refuses
  C2 (`Row.trailing` re-typed in `eff_manifest.txt`) and C3 (the metadata fixture
  `row-populated` re-encoded), and the policy has no name for either. The policy file names the
  two constructors and says so in its comment; accepting the row encoding is the owner's ruling.
- **Truth lane not run.** `scripts/check-truth.py` stops in `harness/truth/Truth.lean:378` on
  `Program.calls`, which no source declares at `4a596d5b` (pre-existing). The pScope pins were
  compared by a scratch render instead: a finite comparison, not the host lane.
- `make check-gen` not run: a derived re-cut rewrites `src/Effect4/Laws/Program/TyView.lean`,
  because commit `7334f119` hand-edited that generated file without its generator. Left at HEAD;
  filed as a separate task.
