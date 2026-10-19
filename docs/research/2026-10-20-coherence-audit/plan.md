# The coherence audit: plan and log

Coordinator: the main session, written 2026-10-19 for a run on the morning of 2026-10-20. The run
is the workflow in this folder, `workflow.js`.

## 1. The one thing to know

Bloat is a modeling error. Where a construct exists that the desired behavior does not need, the
model missed a case, or the code misused a pattern. The audit models each core area from its
semantics first. Then it maps every construct onto that model, and names the misused case or
pattern behind each surplus. Last, it plans the smallest change that keeps every observation. The
owner, 2026-10-19: "if there's bloat, it means that we didn't model our system properly". Also:
"the elegance comes from minimality with regards to desired behavior".

## 2. Why now: the log of 2026-10-19

- Codex's quality review found reproduced defects (`2026-10-19-quality-review/codex-review/`), and
  decisions row 417 ruled the four choices it raised.
- The repair wave's coherence pass (`2026-10-19-quality-review/coherence.md`) modeled the store
  before its fixes. Three of the store seat's six fixes turned out to be deletions or merges:
  - `E4_cas.verify` is a hand copy of `checked_image`;
  - the pack parses a record's header twice;
  - four directory-sync copies each swallow errors.
- The same pass found that the write-ahead log has no consumer outside the store. The pack's
  published boundary already gives every commit the all-or-none promise that the log fails to keep.
- Seat R1 runs in the main checkout under that note. It holds the log's three fixes until the owner
  rules on coherence.md §5.
- The owner concluded that every area likely has the same modeling error. So the owner asked for
  this audit across the core, instead of fixes one finding at a time.

## 3. The method

Each area's mapper does these steps in order:
1. **Model.** State the area's desired behavior in the semantics' terms: its sorts, the operations
   a client needs, the observations that must hold, and its boundaries. Semantics comes before
   mechanism. A construct is justified by an observation it serves, a measured need or a boundary.
2. **Inventory.** List the area's modules, types and definitions, with counts from a command.
3. **Map.** Put each construct against the model element it realizes. Six kinds of surplus follow:
   - one fact with two owners;
   - a construct with no consumer;
   - casework where the model has a fold, a table or an algebra;
   - a failure the model calls a refusal, which the code swallows or raises;
   - a wrapper that only renames, or a one-off beside a shared helper;
   - a definition away from its owner.
4. **Root cause.** Name the misused case or pattern behind each finding. Findings with one cause
   share its name, so the plan removes the cause once.
5. **Minimal target.** Give the smallest shape that keeps every observation, and what it deletes.
   A target that adds more than it removes is not a finding. A new abstraction must replace at
   least two owners.
6. **Evidence.** Each claim has its command and its output. Two constructs are duplicates only if
   they serve one observation.

An adversarial verifier then takes each area's findings. It tries to refute each one: a consumer
the mapper missed, a different observation, a counterexample, or a target that adds more than it
removes. One synthesis groups the surviving findings by root cause and plans the slices.

## 4. Scope

| Area | Paths | Lines |
| --- | --- | ---: |
| The Lean session face | `src/Effect4/Tool`, `Laws/Tool`, `Api`, `Run`, `Laws/Run`, `tools/Drivers` | about 32,000 |
| The Lean program core | `src/Effect4/Program`, `src/Effect4/Data` | about 36,000 |
| The Lean data plane | `src/Effect4/Store`, `Laws/Store`, `src/Effect4/Schema` | about 29,000 |
| The lowering compiler | `src/OCaml5`, the generators under `scripts/`, the hand files of `ocaml/gen`, `ocaml/lcnf`, `ocaml/tools` | about 23,000 |
| The OCaml store | `ocaml/engine/cas` | about 23,500 |
| The OCaml engine and kit | `ocaml/engine` without `cas`, `ocaml/eff`, `ocaml/clock` | about 26,000 |

Out of this run, and logged as such by the workflow:
- the machine (`src/Effect4/Machine`, `Laws/Machine`);
- the program proofs (`Laws/Program`, 613 files and 187,639 lines);
- `ts/`, `harness/` and `rocq/`.

Proof bloat calls for its own method (one lemma per predicate, folds over casework), so it gets a
run of its own.

## 5. The run

- **Agents:** six mappers, each piped into its own verifier as soon as it finishes, then one
  synthesis, for 13 agents. That is above the session's default size of ten, because the owner
  asked for the whole core with verification.
- **Write scope:** every agent is read-only on tracked files. Each writes only its area's note and
  probes in this folder.
- **Report:** the synthesis writes `README.md` here. It holds the root causes, the ranked cuts, the
  slices in order and the owner's decisions.
- **Start:** after seat R1 has finished, so that the store's mapper reads the repaired store.
- **Wave 3:** seats R2 and R3 and E6 wait for the audit's plan, which may reshape them.
- **Command:** run the workflow with `scriptPath` set to
  `docs/research/2026-10-20-coherence-audit/workflow.js` and `args` set to
  `{"outDir": "docs/research/2026-10-20-coherence-audit"}`.
