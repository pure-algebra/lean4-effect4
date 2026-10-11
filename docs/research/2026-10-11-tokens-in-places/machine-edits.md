# Census: invariants re-proved through every helper (2026-10-11)

The owner, 2026-10-11: run the census of `Handles` and `MaskRuns`, and give Codex the biggest head
start, so that improved code keeps landing. This note is the census, the model, a checked probe and
the migration order. `CODEX-PROMPT.md` item 10 points here.

**First, what to know.** Sixteen law modules each prove a machine invariant by re-unfolding every
driver helper: about 210 helper lemmas, in a matrix of invariants by helpers. Every helper is a
short word of primitive machine edits. So prove each helper's word once, and prove each invariant
once per primitive edit. The matrix becomes about 22 decompositions plus 16 invariants by 10 edits,
and most of those cells close by a frame rule. Today's build break shows the cost of the matrix:
R2 changed `interruptRecord`, and two modules that re-unfold it broke.

## 1. The census

Helper-named theorems per module (`spawn_`, `start_`, `exitFiber_`, `fireObserver_`,
`launchEntrant_`, `linkScope_`, `interruptRecord_`, `interruptEach_`, `countdownPark_`, `settle_`,
`driveStep_`, `beginRace_`, `postTask_`, `drainOwed_`, `forkFinalizers_`, `injectYield_`), measured
at `codex/last-planned-goals` `23d070d77`:

| Module | Lines | Helper theorems | Private evaluator analyses | Invariant |
| --- | --- | --- | --- | --- |
| `Machine/Handles` | 6,613 | 43 | 51 | every collected handle names an allocated object |
| `Machine/MaskRuns` | 2,267 | 18 | 26 | a live fiber holds the mask chain at its start flag |
| `Machine/Approximation` | 1,744 | 16 | — | the trace only grows (`Extends`) |
| `Program/Guard/Core` | 3,766 | 12 | 32 | guard-token ownership |
| `Program/Simulation/Actions` | — | 9 | — | the simulation's action relation |
| `Api/Supervision` | — | 9 | — | supervision facts |
| `Program/CommandFrames` | — | 8 | — | command frames |
| `Machine/Scheduling` | — | 8 | — | dispatcher and arming |
| `Program/Guard/MemoIds`, `Guard/ForkLedger`, `Machine/ForkLedgerInvariant` | — | 7 each | — | memo ids; the fork ledger |
| `Program/Guard/FrameOwned` | — | 6 | — | frame ownership |
| `ReleaseCustody/CommandStackSteps`, `Guard/Observer`, `Machine/ForkLedger` | — | 5 each | — | custody; observers; forks |
| `Machine/Ledger` | 520 | 15 (`same_*`) | — | the stack ledger's bookkeeping |

`Machine/Clauses` also has 43 helper theorems. It stays: each is a census witness of one rc.112
arm, a clause of what the machine does, not a preservation proof.

`Handles` splits by section:

- about 730 lines collect the handles of values and code: folds;
- about 530 lines keep handles through the frame machine: a frame-move law;
- about 3,100 lines walk the machine's operations and the driver helpers, including 26 `withFiber`
  arm lemmas and about 1,080 lines for `evaluatePrim` alone;
- about 1,400 lines prove the stores' interpreter key-bounded.

## 2. The model

Separation logic proves a program from a small axiom per primitive command and one frame rule.
The source is O'Hearn, Reynolds and Yang, "Local reasoning about programs that alter data
structures", CSL 2001. Region logic does the same for global invariants. An invariant whose read
footprint misses a command's write footprint survives the command. The sources are Banerjee,
Naumann and Rosenberg, ECOOP 2008, and Kassios's dynamic frames, FM 2006. The driver is such a program over the machine record:

- **The primitive edits** are first-order data with their payloads: `update`, `emit`, `arm`,
  `disarm`, `halt`, `updateRace`, `appendFiber`, `bumpId`, `addFork`, `setState`, and the edits R2
  adds. `Keeps.lean` already states the small axioms of two of them (`update`, `emit`).
  `Approximation`'s tactic `trace_leaf` lists seven of them implicitly.
- **A helper is a word** of edits. Its decomposition theorem is the only place that unfolds it.
- **An invariant is proved per edit.** Most edits miss an invariant's footprint and close by the
  frame rule of a word. The edits that hit it owe a local fact about their payload.

The ledgers are the same structure measured in a monoid. A count ledger sums in `(ℕ, +, ≤)`. The
handle invariant collects in lists of handles under inclusion. The per-edit law of a measured
invariant is the balance of `Moves.balance`, at another monoid.

## 3. The probe

`probes/MachineEdits.lean` compiles with `lake env lean -DwarningAsError=true` against the built
`Effect4.Laws.Machine.Approximation`. It is a finite probe:

- `Edit`, ten tags, and `Edit.apply`;
- `Edit.apply_trace`, the trace's small axiom: an edit appends its own events;
- `run_extends`: every word extends the trace, by one induction;
- `run_keeps`: a projection that every edit of a word keeps is kept;
- `spawn_word` by `rfl`; `start_word` and `postTask_word` by one case split each;
- trace growth for `spawn` and `postTask`, and the races kept by `spawn`, each read off the word in
  one or two lines.

`Approximation` proves the same facts with one lemma per helper and a tactic with `first` and
`try`.

## 4. The migration, in order

1. **Land the alphabet.** `Laws/Machine/Edits.lean`: `Edit`, `apply`, `run`, the small axioms of
   every edit (`Keeps` rows), `run_extends`, `run_keeps`. Extend `Keeps.lean` in place, do not copy
   it.
2. **Decompose the helpers that R2 does not touch.** One theorem each: `spawn`, `start`,
   `launchEntrant`, `forkFinalizers`, `postTask`, `injectYield`, `exitFiber` with `exitStore`,
   `fireObserver`, `beginRace`, `drainOwed`, `arm`, `disarm`, the flush and fire helpers.
3. **The pilot: `Approximation`.** Its sixteen helper lemmas and the `trace_leaf` and
   `trace_chain` tactics become instances of `run_extends`. Record the lines before and after.
4. **`Ledger.Same`.** Its fifteen `same_*` lemmas become one per edit.
5. **R2's helpers.** The R2 migration rewrites join, `countdownPark`, `linkScope`, `interruptAs`,
   `interruptRecord` and `settle`. Its deliverable includes their words, with the message edits
   (`observe`, `dropToken`, `interrupt`) as tags.
6. **`MaskRuns` part B, then `Handles`, then the guard modules.** Each keeps its statements and
   proves its invariant per edit. `Handles` also moves its handle collection onto the generated
   folds (the native code fold, and `Store.Val`'s), and its frame section onto the labelled
   moves.
7. **Measure at each step**, in the merge audit: helper theorems and lines removed.

Each step keeps every existing theorem's name and statement. A connector proves the old statement
from the new structure, the callers move, and then the old proof goes.

## 5. Placement

- Concept: `reactive-scheduling`, invariants over execution traces (`docs/core/semantics.md`).
- Question: the proposed structure claim `machine-edits`, the machine half of `evaluation-moves`.
- Reach: every driver helper that has a word, at every interpreter and machine.
- Limits: a word states what a helper writes, not that the helper is correct. An invariant's
  per-edit facts still owe their payload conditions. No progress follows.
- Unlocks: every machine invariant, present and future, at one fact per edit. It also unlocks
  the place ledger of `README.md` (P1) and the store lift of `model-first.md`.
