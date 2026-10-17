# Receipt: the native kit (2026-10-16)

**The one thing to know before merging.** The branch adds a product face, `ocaml/kit`, made by LCNF
from two new core modules, and three declared facts that rest on the Rocq development. The facts
use a new command, `declared … from` (`tools/ProofGraph/Declared.lean`). It is the owner's
exception to the proof gates, which a decisions row should record. Without the row, the gates count
the facts as three planned goals.

## Base and head

- Base: `719e039bf` on `refactor/phase1-phase3`.
- Head of the work: `da8cef812` on `claude/eff-kit` (worktree `interesting-volhard-6ceb2e`); this
  receipt is the commit after it. Not pushed.
- The commits, oldest first: `a5333bd5d` (the kit), `fb67295f3` (exploration), `8fa5ada0c`
  (generators), `7b9e57e7d` (the session tool), `da8cef812` (the view).
- The research commits of the same session stand on `claude/interesting-volhard-6ceb2e`
  (`2051d3249`, `ab813f61d`): the Rocq files the declared facts cite.

## Changed files

| Area | Files |
| --- | --- |
| Lean, new | `src/Effect4/Run/Tree.lean`, `src/Effect4/Run/Kit.lean`, `src/Effect4/Laws/Run/Tree.lean`, `tools/ProofGraph/Declared.lean` |
| Lean, edited | `src/Effect4.lean`, `src/Effect4/Run.lean`, `src/Effect4/Laws.lean` (one import each), `tools/ProofGraph/Plan.lean` (prints a citation), `tools/Tools/Session.lean` (three operations; the repair of `run`), `src/OCaml5/Lcnf/Builtins.lean` (the row `UInt64.ofNat`) |
| OCaml, new | `ocaml/kit/`: `kit_gen.ml` (generated), `kit.ml`, `kit.mli`, `kit_json.ml`, `kit_author.ml`, `kit_author.mli`, `kit_machine.ml`, `kit_machine.mli`, `kit_serve.ml`, `kit_view.ml`, `bin/eff.ml`, `test/test_kit.ml`, `test/write.lean`, `test/verdicts.txt` (generated), the dune files |
| OCaml, edited | `ocaml/dune` (the folder `kit`), `ocaml/engine/dune`, `ocaml/engine/dune-project`, `ocaml/engine/bytes/dune` (the engine is public), `ocaml/gen/roots.json` (the artifact `kit_gen.ml`), `ocaml/gen/closure-kit_gen.tsv` (generated), `ocaml/README.md` |
| Build and documents | `Makefile` (the kit in `LCNF_OUT`, `GENERATED_PATHS`, the fixtures and `check-ocaml`), `scripts/generate.py` (the kit's fixture folder), `docs/GENERATED.md`, `docs/research/2026-10-16-native-kit/README.md` |

## Commands and their results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4 Effect4.Laws Tools.Session ProofGraph.Plan ProofGraph.AxiomAudit` | `Build completed successfully (1384 jobs)` |
| `lake env lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean --recipe ocaml/gen/roots.json --one 6` | `closure: 1300 of --cap 4000`, `todos (0)` |
| `lake env lean -M4096 --run ocaml/kit/test/write.lean` | `wrote ocaml/kit/test/verdicts.txt` |
| `cd ocaml && opam exec --switch=effect4 -- dune build` | no output: the whole estate builds |
| `cd ocaml && opam exec --switch=effect4 -- dune test eff gen clock kit` | `test_lean_wire: 125 checks, 0 failures`; the clock passes; `test_kit: 51 checks, 0 failures` |
| `cd ocaml && E4_LEAN_CORPUS=… opam exec --switch=effect4 -- dune test engine` | `== ALL PASS: 0 failure(s) ==` |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-native-kit/README.md docs/research/2026-10-16-seat-native-kit-receipt.md` | `PASS` |

The lane's own counts:

- T3: Lean's JSON prints of 408 programs read back, and the kit prints them.
- T5: 408 of 408 of Lean's verdicts are equal.
- T8: 95 of 95 corpus programs in the fragment agree between the tree and the machine.

## Axiom output

`#axiom_audit Effect4.Run.Tree Effect4.Run.Kit Effect4.Laws.Run.Tree`: 355 declarations within
`[propext, Quot.sound]`, 2 of them modulo planned goals; 3 planned goals. The three goals are the
declared facts. `#plan_status` prints each one's citation, for example
`declared: proved in docs/research/2026-10-16-itrees/rocq/BudgetDefs.v: denoteD_approx, denoteBD_approx`.

## Placement of the landed statements

| Statement | Concept and requirement | Status |
| --- | --- | --- |
| `Tree.ofProgram_approx` | `translation-simulation`, R12 | declared (Rocq `denoteD_approx`) |
| `Tree.ofProgram_eq_denoteRowsB` | `translation-simulation`, R6 | declared (Rocq `denoteBD_same`) |
| `Tree.settles_of_ends` | `translation-simulation`, R12 | declared (Rocq `adequacyD`) |
| `Tree.runFrom_approx` | step of `probe_stable` | proved |
| `Tree.probe_stable` | consumer: `settle_sound`, the session tool's `settle` | modulo `ofProgram_approx` |
| `Tree.settle_sound` | consumer: `Kit.settle`, `eff run`, the session tool | modulo `ofProgram_approx` |

## Open obligations

- Decisions rows for the coordinator, written in the note's last section:
  - the declared facts;
  - the kit as a product face;
  - row 408 (3) amended: Rocq backs declared facts and stays out of every gate.
- `generated/corpus-index.tsv` is stale against the checker at the base (9 programs, the note's
  finding 1). `make corpus` writes it again; this branch does not.
- Raw formation is not lowered: the route does not spell `ArgF.child`'s dependent field.
- The generator's walk and the arms beyond `Budget.v`'s fragment rest on the differential T8, not
  on a Rocq proof.

## Bounded or host-only evidence

- T3, T5 and T8 are finite checks on 408 programs, not theorems.
- The timings are wall times on a shared machine, 20 runs each.
- No `make check-full`, no `check-ts` and no `make check-gen` ran.
- The MCP server ran in-process (T10) and from a scripted client, not under a real MCP client.
