# The coherence audit: plan and log

Coordinator: the main session, written 2026-10-19 for a run on the morning of 2026-10-20. The run
is the workflow in this folder, `workflow.js`, and every agent reads `orientation.md` first.

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

The owner narrowed the run the same evening: three agents, conceptual rather than specific, and
oriented first in the project's philosophy, pedagogy and inspirations. "Our goal is to maintain
that coherence of patterns, ideas, and inspirations especially when we refactor."

The orientation is `orientation.md` in this folder. The coordinator wrote it from the
authorities, the dated organizing principle, the memory of the owner's steers, and 184 of the
owner's messages since 2026-08-31. Every agent reads it before any code.

Each reader does three things:
1. **Pattern map.** For each pattern of the organizing principle, say where the area honours it and
   where it departs. The patterns are:
   - one free object per sort;
   - the five arrow kinds and their obligations;
   - the five constructions;
   - tables as data, with generation as a fixed point;
   - one located refusal per judgment;
   - one owner per fact;
   - the host boundary;
   - deep modules.
2. **Strengths.** Name what already exhibits the patterns cleanly, so no refactor breaks it.
3. **Departures.** Give at most ten, each at the level of a pattern. Each names the modeling error
   behind it and a few representative declarations. Each gives the conceptual move that restores
   coherence, what that move deletes, and what must stay because it serves a distinct observation.

The synthesis first tries to refute each departure. It checks for:
- consumer-count reasoning;
- a false duplicate, where two constructs serve different observations;
- an over-engineered move;
- an unnamed ruling.

Then it groups what survives by root cause. Each cause gets one design rule that removes the class.
The refactor is planned as ordered moves, each making the next smaller.

## 4. Scope

| Reader | What it reads |
| --- | --- |
| The Lean core | `src/Effect4/Tool`, `Api`, `Run`, `Program`, `Data`, `Store` and `Schema`, with `tools/Drivers/Session.lean`; the session face and the program and data plane under it |
| The compiler and the OCaml estate | `src/OCaml5`, the generators under `scripts/`, and `ocaml/` in the large, read as one compiler with one runtime |

Out of this run, and logged as such by the workflow:
- the machine (`src/Effect4/Machine`, `Laws/Machine`);
- the program proofs (`Laws/Program`, 613 files and 187,639 lines);
- `ts/`, `harness/` and `rocq/`.

Proof bloat calls for its own method (one lemma per predicate, folds over casework), so it gets a
run of its own.

## 5. The run

- **Agents:** two readers in parallel, then one adversarial synthesis.
- **Write scope:** every agent is read-only on tracked files. The readers write `lean-core.md` and
  `compiler-estate.md` here, and the synthesis writes `README.md`.
- **Report:** `README.md` holds the root causes, the design rules, the ordered moves, the strengths
  to preserve and the owner's decisions.
- **Start:** after seat R1 has finished.
- **Wave 3:** seats R2 and R3 and E6 wait for the audit's plan, which may reshape them.
- **Command:** run the workflow with `scriptPath` set to
  `docs/research/2026-10-20-coherence-audit/workflow.js` and `args` set to
  `{"outDir": "docs/research/2026-10-20-coherence-audit"}`.
