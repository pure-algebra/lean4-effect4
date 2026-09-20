# Phase C close receipt

Base: the Codex landing at `ac4a0fe5` plus the review at `92168604` and the connector
commit `b2bf4cca`. Branch `refactor/phase1-phase3`, nothing pushed, `README.md` untouched.
The bank mechanism did the closing; where it did not, the obligation stays wanted and the
reason is recorded below. Every number here is read from the build and check logs of this
session, not from the earlier receipts.

## 1. What landed

- **The store banks are split.** `Effect4.Stores` carries equations and laws only;
  `Effect4.StoreKernel` carries the store definitions and the arena view, used inside
  `CompletionData`, `Arena`, `RefKernel`, `Refinement`, `StoresLaws` and Handles' own store
  proofs; `Effect4.Fibers` is the fiber machine's clause bank. Declared in
  `Laws/Auto/RuleSets.lean`.
- **The thirty connector statements are closed** (`Laws/Machine/Refinement.lean`): the
  functor, naturality, image, Projects and Factors laws, the arena Projects instance,
  `completionPrim_injective` by the exit readback, `deferredOk_iff_image`.
- **The World order is proved** (`Laws/Program/Typed/World.lean`): table extension is a
  preorder, the world order is a preorder and a `WorldOrder` instance, the two column
  clauses with coverage recover the keywise judgments, `heapNat_iff`, the fork, refMake and
  deferredMake extension theorems, the five closed controls and `heapNotMonotone`. One
  statement stays wanted (§3).
- **The Arena red controls are decided** (`Test/Machine/Runtime/ArenaContract.lean`).
- **Origins at the machine and at the source** (`Laws/Api/Supervision.lean`): `spawn`,
  `start`, `launchEntrant`, the three fork arms and the race launch record the site on the
  fiber; the located `fork`, `forkIn`, `forkScoped`, `raceAll` and the two-entrant race
  decode to their action and stamp. `race?_updateRace_same` for the race table.
- **The fork-source bridge** (`Laws/Program/Typed/ForkSource.lean`) is proved as
  `fork_source_extension`; its obligation stays wanted because the search does not reduce
  the `let`/`∃` statement to it (§3).
- **The ledger reports every miss at once** (`Laws/Auto/Obligations.lean`): a gate now
  collects the missing and stale names and fails once with the whole list, so one build
  shows a scope's residue. The two audit controls carry the new message texts.
- **Instance hygiene.** 130 theorems in `Clauses`, `Approximation`, `Book` and
  `Supervision` carried `[DecidableEq …]` binders they never used (those files silence the
  linter). A `def` obligation does not pick those binders up, so the search could never
  synthesize them and the theorem could never apply. Each now carries an `omit … in`,
  found by running the linter to a fixpoint (three rounds).
- **Registrations.** 83 backing theorems entered the banks. The shape rule that survived the
  builds: a single equation or Prop whose goal has no `if`/`match`/`let` → `unsafe 90% apply`;
  a whole-statement rule that must fire before aesop's own `assumption`/`rfl`/`split`/`And`
  rules → `safe -100 apply` (aesop runs safe rules in ascending priority); an equation
  whose right side is a `let` block → `norm simp`; an implication whose premises are all in
  context → `safe forward`.

## 2. Numbers

| Measure | Value |
|---|---|
| Ledger gates | 65 |
| Statements under gates | 393 |
| Closed by the gate search | 351 |
| Open | 42 |
| Live wanted markers in `src` | 44 (46 with the two audit fixtures) |
| Bank registrations: Stores / StoreKernel / Fibers / TypedState | 129 / 4 / 91 / 10 |
| `make build` | green, 690 jobs |
| `make check` | see §4 |
| Source diff over the review base | 24 files, +1,090 / −140 |

## 3. The open forty-two, by cause

1. **Not yet proved (11).** The five static-membership sites (`source_*_site`,
   `source_two_race_sites`: the fold-to-`Node.at_` bridge is not written), the two trace
   agreements (`step_agrees`, `reachable_agrees`: a whole-step invariant), the M4 park
   handshake (held by design), `observe_replace_trace` (`rfl` refused; the observation's
   `inspect` needs a lemma, not an unfold), and one audit fixture that is open on purpose.
2. **Proved as a theorem, not reduced by the gate search (31).** The theorem is in the tree
   and compiles; the obligation keeps its marker because aesop's normalisation changes the
   goal or the context before the bank rule can fire:
   - `subst` consumes an equation hypothesis the rule needs as a premise
     (`fork_arm_minted`, `spawn_minted`, `withFiber_fork_minted`, `memoBuild_extension`,
     `storesOk_closeScopeUnsafe`, `scopeLinkFiber_ok`, `dropFinalizer_ok`, the three
     `*_pendingOk`, `book_advanceState`);
   - `simp` with the Stores bank rewrites one conjunct or hypothesis first (`complete_keys`,
     `register_keys`, `drainDue_keys`, `setCell_*`, `spawnChild_keys_subset`);
   - `simp` with `withFiber_fork` rewrites the goal's fork term before the equation rule
     matches it, while removing that rule breaks the obligations that close through it
     (`fork_forked`, `forkScoped_forked`, `supervision_static` ×2, `source_fork`,
     `race_launch_origins`, `forkFinalizers_forked`);
   - the goal is a `let`/`∃`/`∀` shape the apply builder does not index
     (`fork_source_extension`, `actionAt_*`, `fork_rel`, `forkIn_rel`, `raceAll_rel`).
   The fix is one of: state the rule in the goal's normal form, register the conjuncts
   separately, or give the gate a tactic that applies the theorem before normalising.
   None of these change what is proved.

## 4. Checks

- `make build`: green, 690 jobs (`Test` built last).
- `make check`: green. The fresh root and axiom audit passed; `check-gen` reports
  "every Lean-only generated file is what its generator emits". No group producer ran for
  the runtime cuts: Phase C changed no runtime source, so LCNF, CAS and EFF are untouched.
- Coverage, from `scripts/report-effect-runtime-coverage.sh` at the working tree:

```text
Effect rc.112 runtime coverage: denominator 135; owned-with-green 8/135;
green 133, partial 2, absent 0; census 137 rows, 2 excluded
partial: op.Failure layer.launch-holds-scope
```

## 5. Not done

- **The memo slice** (the review's F3: `MemoKeysFresh`, `memoEntry_keys` under it, the
  deletion of the identity write) is not started. It is a runtime change and needs its own
  regeneration and OCaml validation; it is left for its own commit.
- **The full-driver trace agreement** (`step_agrees`) and the static-site bridge are the
  two proof projects that remain in Phase C's residue.
