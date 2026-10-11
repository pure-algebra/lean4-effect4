# Goals packet: the store invariants of the atomic scenario

Family `store-invariants`. Goals `bounded`, `counted` and `committed` of
`Test/Dogfood/Scenario/Atomic.lean`, on the program `shop`. Concept `store-typing`, requirement R4.
Branch `probe/goals-store-invariants`, based on `refactor/phase1-phase3` at `5b40699ae`.

## 1. First: what the coordinator must know

- **`bounded` rests on one general lemma and nothing else.** That lemma is the cell invariant from
  write sites, `heap_sites_keep`. The probe proves every program-specific step of `bounded`. The tree
  has no such law. Its nearest kin is the typed state (M6). M6 keeps one predicate, "a member of the
  declared type", and records no provenance of a write's term.
- **`counted` and `committed` follow from no one-cell invariant.** They need each request's position
  in its code. Each request decides once and deposits once, and a planted-failure exit follows its
  deposit and its note. The probe proves the algebra from a ghost stage of each request to both goals.
  The stages are one program-specific planned goal, `shop_stages`.
- **The large open cost is one general law the tree lacks: each fiber's position in its own code
  (G2).** All four families likely need it. Section 4.4 sizes it.
- **No goal of the family is false, as far as this probe can tell.** The DOGFOOD seat's search
  found no run against them in 606420 scripts. A reading of the machine finds no hostile move that
  breaks the invariants (section 9); that reading is assumed, not proved.
- **The worktree base was stale.** The seat's worktree started at `main` (`9187b9b60`), which has no
  `Test/Dogfood`. The branch was re-pointed at `refactor/phase1-phase3` (`5b40699ae`), the main
  checkout's branch. The other probe worktrees made at `9187b9b60` meet the same trap.

## 2. What the probe establishes

`Probe.lean` compiles with `lake env lean` in the worktree in about 9 s, with no error and no
warning. Its `#plan_status` lines report each node's standing. They fail on any axiom outside
`[propext, Quot.sound]` that a node's proof reaches, goals excluded (`ProofGraph.Proof`,
`disallowedAxioms`).

| Declaration (`Probe.lean`) | Standing | What it states |
| --- | --- | --- |
| `bounded_modulo` | modulo `heap_sites_keep` | `Bounded` |
| `counted_modulo`, `committed_modulo` | modulo `shop_stages` | `Counted`, `Committed` |
| `family_modulo` | modulo both goals | `Bounded ∧ Counted ∧ Committed` |
| `RunKeeps.scenario`, `reached_history`, `scenario_history`, `history_keeps`, `scenario_control` | proved | the frame (section 3) |
| `counted_of_fit`, `committed_of_fit` | proved | the observation algebra: stages to `counted` and `committed` |
| `shop_sites_used`, `shop_census` | proved | the shop's 31 write sites keep the used bound |
| `decision_keeps_used`, `deposit_keeps_used`, `refill_keeps_used`, `note_keeps_used` | proved | each family of sites keeps the bound |
| `racy_breaks_used` | proved | red control: the racy write site does not keep the bound |
| `decision_coherent`, `erased_incoherent` | proved | the decision's answer agrees with its counts; the erased term's does not |

`Measure.lean`, beside the probe, prints the numbers this note quotes: 31 sites, 23 shapes and 33
shapes. They are finite probes.

## 3. The frame (stated for the coordinator's unification)

No declaration of the frame exists in the tree. A search for `RunKeeps` and `play_keeps` found none.
Every name below is the probe's and is proved.

- **The run frame.** `RunKeeps (I : Run → Prop) : Prop := ∀ s c, I s → I (s.step c)`.
  `RunKeeps.play` carries it over rows, and `RunKeeps.scenario` over a script of moves.
- **From a run to its machine.** One row moves a run's machine by at most one accepted decision
  (`step_machine`). `Accepted table calls m d` holds of a control, or of an answer that preflight
  returned at that machine. `applyReply_machine` and `advance_machine` give the two cases, and
  `preflight_accepted` the answer's acceptance.
- **The history.** `HistoryOf b cf m` holds when `m` is the load stepped by a `Lift.Admitted` history
  of `steppedBy`, each decision accepted where it was met. `reached_history` gives it for every
  reached run, and `scenario_history` for every script's run. `history_keeps` carries a machine fact
  along a history by `Lift.foldl_lift` (`src/Effect4/Laws/Machine/Lift.lean`).
- **Control histories.** With an empty row table `admit` refuses every answer, so every accepted
  decision is a control (`accepted_nil_control`, `history_control`). `scenario_control` gives the
  shop's every run as a control history (`ControlHistory`).
- **The observation of a machine.** `observeM` reads the machine only, and `observe_eq` is `rfl`.

The frame lives at the machine because every invariant of the family reads cells and fibers only.
`step_machine` makes each row a `steppedBy` step or no step, so a machine invariant suffices.

Placement proposed for the frame: concept `host-session-protocol`, requirement R13, beside
`Test.Dogfood.Scenario.replays`, whose consumer is every scenario. Question: a new registry claim
`run-history`, role compatibility. Limits: it carries an invariant and proves none; it states no
progress.

## 4. The central question: a cell invariant from write sites

### 4.1 What exists

| Name and path | What it gives | Why it is not the law |
| --- | --- | --- |
| `step_keeps_cell`, `step_updates` (`src/Effect4/Laws/Step/Store.lean`) | one `Ref.modify` step keeps its cell's type | one step; typing only |
| `fold_typed_atomic_update`, `refModify_typed_step` (`src/Effect4/Laws/Program/Typed/ListFold.lean`) | one typed modify step | one step; typing only |
| `typedState_reachable`, `reachable_typed`, `obs_typed` (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`) | every reachable reference machine is typed; every heap cell fits its declared type | the predicate is fixed to `Fits`; no provenance of a write's term |
| `storePre`, `Ψ_S` (`src/Effect4/Laws/Program/Typed/Residual.lean`) | a heap write demands `TermMaps` at the cell's declared type | semantic; any term of the right type passes |
| `StoresOk` with `MachineOk` (`src/Effect4/Laws/Program/Simulation/Hooks.lean`, `src/Effect4/Laws/Machine/Book.lean`) | a frame-machine store invariant carried by the Book | about deferred cells' programs |
| `Lift.DecisionLift`, `machineFact_stepDecision`, `foldl_lift` (`src/Effect4/Laws/Machine/Lift.lean`) | the generic lift from commands to decisions and histories | a frame; the invariant is the caller's |
| `stepAgrees`, `hooksAgree_of` (`src/Effect4/Laws/Program/Simulation/Drive.lean`), `book_stepDecisionState` (`src/Effect4/Laws/Machine/Book.lean`) | the frame machine and the reference machine agree step by step: equal stores, equal exits | a transfer, not an invariant |
| `MintedAt`, `KeyBounded` (`src/Effect4/Laws/Machine/Handles.lean`); `handles_minted` (`src/Effect4/Laws/Program/Handles/Evaluation.lean`) | a closure invariant over every carrier of the machine, generic in the name collector | its predicate is "the handle exists", Boolean and store-dependent |
| `Guard.Reachable`, `executePrefix` (`src/Effect4/Laws/Program/Guard/Core.lean`) | reachability of the frame machine by `(fuel, decision)` prefixes | no cell fact |
| `meaning_onExit` (`src/Effect4/Laws/Program/Denote.lean`) | a finalizer runs on the stores its body left, in the single-fiber denotation | one fiber; see section 7 |

So the tree has the lift, the transfer and a closure skeleton. It lacks a cell law for an arbitrary
predicate, and it lacks any law about a fiber's position.

### 4.2 G1: the cell invariant from write sites (`heap_sites_keep`, general)

```lean
def HeapOk (P : Val → Prop) (refs : RefHeap) : Prop :=
  ∀ (i : Nat) (v : Val), refs[i]? = some v → P v
def OpKeeps (P : Val → Prop) (o : SyncOp) : Prop :=
  ∀ (s s' : Stores) (ans : Val), syncOpStep o s = some (s', ans) → HeapOk P s.refs → HeapOk P s'.refs
def levelAt : Node NativeOp → Nat → List Nat → Option Nat   -- the binder table along a path
def SitesKeep (root : NativeEff) (P : Val → Prop) : Prop :=
  ∀ path op request env val o, Node.at_ (.eff root) path = some (.eff (.perform op request)) →
    levelAt (.eff root) 0 path = some env.length →
    evalTerm env request = some val → NativeOp.syncOpOf op env val = some o → OpKeeps P o
proof_goal heap_sites_keep (b : Api.Built) (compileFuel : Nat) (P : Val → Prop)
    (sites : SitesKeep b.program P) : ∀ m, ControlHistory b compileFuel m → HeapOk P m.state.refs
```

The law is handle-agnostic: a site keeps the predicate at whatever cell it writes, so no alias
analysis enters. Types do not resolve aliasing here either. The environment of a site is the one
its level gives, so a site's term reads the cell where its binder says. A typed environment is not
enough: `PointTyped` (`src/Effect4/Laws/Program/Typed/Admission.lean`) binds its type environment
existentially, and a longer environment would let `var d` read another value.

Placement. Concept `store-typing`, requirement R4. Question: a new registry claim
`cell-invariant-from-write-sites`, role soundness, pointer `heap_sites_keep`. Reach: every built
program, every control history. Limits: one cell at a time, no relation between cells, no fiber
position, no progress. Consumers: `bounded`; every scenario goal that reads one cell.

Its proof needs two parts.

- **G1a, the points are leveled (general).** Every point that occurs in a reachable machine has
  `p.env.length = levelAt root p.path`. Points are built from points that already occur, by
  `Point.child`, `childWith`, `childWith2`, `childBind`, `layerBuild`, `spineChild` and `redirect`.
  Each follows the binder table (`Node.childLevel`, `src/Effect4/Program/Binders.lean`). Statement
  sketch: `∀ m, ControlHistory b cf m → ∀ p ∈ m.points, p.env.length = levelAt (.eff b.program) 0
  p.path`. Here `RunMachine.points` collects over every carrier, as `RunMachine.keys` collects
  handles (`src/Effect4/Laws/Machine/Handles.lean`).
- **The heap frame.** The heap changes only through `syncState` on a thunk of the evaluated
  fiber's code. Such a thunk's store row is a site's row at its level.

Two routes carry both parts.

- **Route A, recommended: the typed state carries a heap predicate.** Add two defaulted fields to
  `ProgramSource` (`src/Effect4/Laws/Program/Typed/Admission.lean`): a predicate `heapPred` and its
  site proof `SitesKeep program heapPred`. Add the predicate to `HeapCell` in `preds`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`). Add the site's provenance to `storePre`'s heap
  arms (`Typed/Residual.lean`). A search for `TypedProg.store` finds every heap-write store node in
  `syncRow_typed` (`Typed/Denotation.lean`). The other constructions are scope, memo and read rows,
  or pass a node through (`Typed/Seq.lean`). `HeapCell` has eight uses in five files.
  `clause_kernel` and `clause_refMake` (`Typed/Commands/Clauses/StoreRef.lean`) then keep the
  predicate from the provenance and `SitesKeep`. M6's ledger then gives it on every reachable
  reference machine, and the Book (`book_stepDecisionState`) transfers it to the frame machine,
  whose store is equal. G1a enters as a strengthening of `PointTyped`: the type environment is the
  one `Node.envAt` gives at the path. Its length should be `levelAt`'s, since both follow the one
  binder table; that equation is assumed here and owed. Risk: M6 is large and its rebuild is slow.
  The defaults keep every existing statement.
- **Route B, fallback: a closure law on the frame machine.** Take a Prop-valued code predicate and a
  store predicate, and per-hook premises for both. Prove once that every command keeps both, on
  every code and on the store. The skeleton is `Laws/Machine/Handles.lean`'s (6558 lines), without
  the world and its growth. The handle closure itself cannot carry it: its collector is Boolean. A
  `refMake`'s provenance also names an environment that the row does not carry.

Sizes. Route A: 20 to 35 hours, plus G1a inside `PointTyped`: 10 to 20 hours. Route B: 40 to 70
hours, G1a included.

### 4.3 What atomicity buys

`bounded` needs atomicity of the decision. The decision checks `used < 3` and writes `used + 1` in
one store step, so the site keeps `UsedOk` on its own (`decision_keeps_used`, proved). The racy
write reads, yields, then blindly increments, and it does not keep the predicate
(`racy_breaks_used`, proved on a window with `used = 3`). With a split read and write no one-step
predicate holds, and the proof would need positions.

`counted` needs coherence instead: the decision's answer agrees with the counts it writes
(`decision_coherent`, proved). The erased term answers the test and leaves the window
(`erased_incoherent`, proved). The racy write is coherent, which is why `counted`'s red control is
`erased` and not `racy`. Atomicity of one update a request makes the stages move with the counts in
one store step. So the relational invariant moves one transition at a time. Atomicity is not what
makes `counted` true.

### 4.4 G2: a fiber's position in its own code (general; needed by `shop_stages`)

`counted` and `committed` relate the stores to each request's progress. "Each request decides once"
is a fact of a fiber's code: after the decision's step, no code in the machine can run the decision
again. "A planted-failure exit follows the deposit" is a fact of program order. Neither is a fact
of one cell.

Statement sketch. A fiber-local step relation `LocalStep root : FrameFiber → FrameFiber → Prop`
evaluates one primitive of one fiber with any store answer. `LocalReach` is its closure with the
interruption edits. Take a machine of a control history and a fiber `f` forked at `site`
(`RunMachine.originOf`, the fork ledger `RunMachine.forks`). Then `LocalReach` reaches `f.frame` from
the compiled fork child at its point. Every store step of the machine is one fiber's local step.
M6's `LiveCode` and `ReadCode` (`Typed/Assembly.lean`) are the semantic sibling: they keep each
fiber's code typed, and G2 keeps it a residual.

Measured shapes. A request fiber passes 23 distinct frame shapes at command boundaries on request
1's path, whose outcome is `admitted`. Request 2 alone passes 33, nine of them its allocations
(`Measure.lean`). One command evaluates one primitive (`evaluatePrim`, `src/Effect4/Machine/Fibers.lean`).
So a budget cut can freeze a fiber at any of those shapes. With the rejected path and the
interrupted unwinding a request has about 40 shapes, parametric in its number. The root has about
60, the daemon about 10.

Placement. Concept `reactive-scheduling` (`docs/core/semantics.md` §2.4, "Invariants over execution
traces", Owicki and Gries). Question: a new registry claim `fiber-local-positions`, role soundness,
proposed. Requirements served: R4, through `shop_stages`, and R11, through `cleans_once`. Limits: an
invariant, not progress; nothing of the OCaml engine or a TypeScript run. Size: 40 to 70 hours.

## 5. Goal `bounded`

**Statement.** Under every script the window's `used` field is at most 3.

**Placement (its docstring).** Concept `store-typing`, requirement R4; a clause of the scenario
claim `atomic`; consumer the atomic scenario. Reach: the program `shop`, every script of the
driver's alphabet, the battery's budgets, natural-valued fields. Limits: a missing field reads as 0;
no scheduler guarantee, host transaction or whole-run resource theorem.

**Evidence today.** Controls (`shopControls`), tested: green "three of five admitted, three used",
green "the refill writes zero", red "the racy shop admits five and uses five". The search is the
DOGFOOD seat's receipt (`docs/research/2026-10-05-seat-DOGFOOD-receipt.md` §5.5, untracked in the
main checkout). It played 17 and 15 moves, length 4 at most, from eight start states: 606420
scripts, none against the four goals. The racy shop fails `bounded` in 18931 of 54240. Not re-run
here.

**Decomposition.**

| Lemma | Status | Kind | Route | Hours |
| --- | --- | --- | --- | --- |
| frame: `RunKeeps.*`, `reached_history`, `history_keeps`, `scenario_control` | proved (probe) | general | land as written | 2 to 3 |
| `heap_sites_keep` (G1) | planned goal (probe) | general | section 4.2 | 30 to 55 |
| `shop_sites_used`: `shop_census` (kernel `decide` on the elaborated shop, about 3 s), `performSites_complete`, `build_elaborates`, the families, the `syncOpOf` inversions | proved (probe) | program-specific, on general tools | land as written | 2 to 3 |
| `bounded_modulo` | proved modulo G1 | program-specific | land, then close | 0.5 |

**Does not establish.** No relation between cells; no fiber's progress; nothing of the OCaml engine
or a TypeScript run.

## 6. Goal `counted`

**Statement.** Under every script `Observation.counted` holds. A request whose outcome is `admitted`
or `failedBehind` has one deposit, and one whose outcome is `rejected` has none. The window's counts
hold every request that exited with a decision. They equal those requests' counts once all six have.

**Placement (its docstring).** Concept `store-typing`, requirement R4; a clause of `atomic`. Reach:
`shop`, every script, the battery's budgets. Limits: an interrupted request's counts stay open; no
claim that a request completes.

**Evidence today.** Controls, tested: green "six completed are four admitted with four deposits".
Green "an interrupted request is counted nowhere". Red "a term that answers the decision and leaves
the window loses every count" (`erased`). Search: as for `bounded`; the erased shop fails `counted`
in 2768 of 3615.

**The relational invariant.** `StagesFit g o` (`Probe.lean`, section 5) gives each request a stage.
The stages are `waiting`, `admitted`, `deposited` and `rejected`. A stage is a ghost: an interrupted
request's stage is not readable once its code is gone. The window's `admitted` count is the number of
admitted or deposited stages, `rejected` the number of rejected ones. A request's deposit stands once
exactly when it deposited. An admitted exit means `deposited`, a rejected exit `rejected`. Request
2's planted failure means a cleanup entry `[2, seen]` with `seen ≥ 1`. `counted_of_fit` and
`committed_of_fit` derive both goals from it (proved).

**Decomposition.**

| Lemma | Status | Kind | Route | Hours |
| --- | --- | --- | --- | --- |
| `counted_of_fit` and its list lemmas | proved (probe) | program-specific algebra | land as written | 1 |
| `shop_stages` | planned goal (probe) | program-specific | below | 30 to 50 on G2 |
| G2 (section 4.4) | not stated in Lean | general | section 4.4 | 40 to 70 |
| `decision_coherent` | proved (probe) | program-specific | the decision's step | done |

Route of `shop_stages`. Define the invariant:

```lean
def ShopInv (m : NativeMachine) : Prop :=
  ∃ g, StagesFit g (observeM m) ∧ RootAt m ∧ DaemonAt m ∧ ∀ i ∈ requests, RequestAt i (g i) m
```

`RequestAt i st m` has three cases. Fiber `i + 1` is absent and `st = waiting`. Or its frame is one of
request `i`'s shapes at stage `st`. Or it exited with an exit that `st` allows. Prove `ShopInv` at
the load. Prove it across every control by `Lift.DecisionLift`, with a queue fact: a command queued
inside a decision names a running fiber at a running shape. The store-side steps are four:

- the decision: `decision_coherent` and the used bound;
- the deposit: the history gains `[id]`;
- the note: the log gains `[id, admitted + rejected]`;
- the refill: the counts stay.

The fiber-side steps come from G2. An interruption freezes a stage.

**Statement check.** `counted` is true. Its clause "`o.admitted + o.rejected ≤ 6`" needs each request
to decide at most once, which only positions give.

## 7. Goal `committed`

**Statement.** Under every script, once request 2 has exited with the planted failure, its commits
stand. Its deposit stands once, and the window's `admitted` count is at least one. Its finalizer saw
a decided request.

**Placement (its docstring).** Concept `store-typing`, requirement R4; a clause of `atomic`. It
names `Effect4.Program.Denote.meaning_onExit` as its supporting law.

**Evidence today.** Controls: green "request 2 fails behind its commits", red "a finalizer that
takes the deposit back". Search: the undone shop fails `committed` in 1421 of 3615, every run that
meets the premise.

**The fragment question.** H8 cannot carry `committed`. `denoteRows_eq_session` and `h8_loopedRows`
(`src/Effect4/Laws/Api/SessionMeaning.lean`, `SessionMeaningLoop.lean`) hold for one fiber. They
admit no fork, interruption, clock step or scope, and `shop` forks seven fibers, sleeps and
interrupts. `meaning_onExit` is a single-fiber denotational law. The scenario already uses it on
`alone` (`unsuspended_runs`). So the run-level route is needed, and `meaning_onExit` has two
run-level parts:

- **the commits stay.** Every write site keeps each cell's `history` a prefix of the next. This is
  a two-state reading of G1: a predicate on a cell's old and new value, kept by each site. The
  deposit appends; the other sites fail on an account or leave its `history`.
- **the finalizer runs after the body, on the stores the body left.** This is a position fact of
  fiber 3 (G2).

**Decomposition.** `committed_of_fit` (proved) plus `shop_stages`. A cheaper route restricts
`shop_stages` to request 2. It needs fiber 3's shapes and the root's fork of it. It also needs the
census fact that only `depositAt 2` writes the amount 2. Its cost is about 60 percent of
`shop_stages`'s.

**Statement check.** `committed` is true. Its docstring's supporting law cannot carry it; the
docstring could name the run-level steps instead.

## 8. The slices for Codex, in order

| Slice | Content | Depends on | Parallel with | Narrow build and audit |
| --- | --- | --- | --- | --- |
| 1 | Land the frame: sections 1 to 3 of `Probe.lean` as `src/Effect4/Laws/Run/Invariant.lean` (general), with placements | none | 2 | `lake build Effect4.Laws.Run.Invariant`; `#axiom_audit Effect4.Laws.Run.Invariant` |
| 2 | Land the write-site toolkit (`read_after_set`, `refModify_step`, `refUpdate_step`, `make_keeps`, `get_keeps`, the evaluation and `syncOpOf` inversions, `levelAt`, `performSites`, `performSites_complete`) as a Laws module, and the shop's census, families and coherence in a `Test/Dogfood/Scenario/` battery | none | 1 | the two modules; `#axiom_audit` on both |
| 3 | G1a and G1 by route A | 1, 2 | 4 | the touched `Typed/` modules and their dependents; `#axiom_audit` on each touched module |
| 4 | G2, the fiber-local positions | 1 | 3 | the new module; `#axiom_audit` |
| 5 | `shop_stages` on G2, with the four store steps | 2, 4 | none | the shop battery; `#axiom_audit` |
| 6 | Replace the three `proof_goal`s of `Atomic.lean` by theorems | 3, 5 | none | `lake build Test.Dogfood.Scenario.Atomic`; `#scenario_gate` |

Totals: `bounded` after slices 1 to 3, 35 to 60 hours. `counted` and `committed` after slices 4 and
5, 70 to 120 hours more. A shortcut for this family alone skips slice 3. `shop_stages`, widened with
the used bound, gives `bounded` too. It leaves no general law for the other families.

## 9. What the probe does not establish

- `heap_sites_keep` and `shop_stages` are planned goals; the three goals are proved modulo them.
- G1a and G2 are sketches, not compiled statements.
- The search counts are the DOGFOOD seat's, not re-run here. The measured shapes are finite probes.
- Hostile moves examined by reading the machine, each keeping the invariants (assumed, not proved):
  - a raw `interruptFrom` with any interruptor and any annotations;
  - `installMiddleware`, `yieldVerdict`, and `fire` at any owner;
  - `advance` by any duration;
  - `evaluate` of any fiber: a no-op on a running, parked or exited fiber (`driveStep`);
  - a budget cut, which freezes a fiber at its shape;
  - interrupting the root, the daemon, or a fiber in its finalizer (masked);
  - interrupting a fiber twice: its outcome is `other`.

  No move creates a fiber or a write outside the program's sites.

## 10. Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=2 lake build Test.Dogfood.Scenario.Atomic Effect4.Laws.Auto.Obligations Effect4.Laws.Program.Guard.Core` | 1026 jobs, completed successfully |
| `lake env lean docs/research/2026-10-10-goals-packet/store-invariants/Probe.lean` | about 9 s; no error, no warning; the standings of section 2 |
| `lake env lean docs/research/2026-10-10-goals-packet/store-invariants/Measure.lean` | about 8 s; prints 31, 23 and 33 |
| `decide` on `(Authoring.elaborateModule (shop .none)).toOption.isSome = true` | succeeds, about 3 s |
| `decide` on `(Effect4.Api.Author.build (shop .none)).toOption.isSome = true` | fails: admission does not reduce |

Axioms: `#plan_status` passes on every node of section 2, so each reaches at most `propext` and
`Quot.sound`, goals excluded. `#axiom_audit` audits imported modules only, and the probe is a
standalone file.

## 11. Traps

- `decide` on `Author.build` gets stuck in admission. Reduce `elaborateModule` instead, and move to
  the built program with `build_elaborates`.
- Import-made ambiguity: the scenario defines `admit` and `request`. Write `Program.admit`.
- `split at h` reverts and renames every local that depends on the split's discriminants, so a
  later name can resolve to a global (`request`). Case on an inductive predicate in its own lemma
  (`Family`, `family_of_siteOk`).
- A `have` in `applyReply` and a `let` in `Author.build` block `split`: `dsimp only` first.
- For a fixed row, `split` on `NativeOp.syncOpOf` keeps the arms of the other rows.
  `simp only [reduceCtorEq, …] at *` closes them (`modify_inv`).
- `nomatch h, …` reads the comma as a second discriminant: parenthesize the lambda.
- `of_decide_eq_true` at a defined `Prop` such as `UsedOk` needs the unfolded type.
- A `fire` skips its remaining tasks once one task runs out of fuel (`fireStep`), so a fuel cut
  hides later fibers' intermediate states. Measure the first fiber of a fire.

## 12. Shared machinery

What this family needs that the other families likely need too:

1. The run frame and the run-to-machine reduction: `RunKeeps`, `step_machine`, `HistoryOf`,
   `reached_history`, `history_keeps`, and `observeM` with `observe_eq` for each scenario.
2. Control histories for a program with no host row: `accepted_nil_control`, `history_control`.
   A program with host rows keeps `HistoryOf`; the typed route then needs `admit_sound`.
3. G1, the cell invariant from write sites, with G1a, the points are leveled.
4. G2, a fiber's position in its own code: every goal about progress, linearity or program order.
5. The write-site toolkit: `read_after_set`, `heapOk_poke`, `refModify_step`, `refUpdate_step`,
   `make_keeps`, `get_keeps`, `eval_recordSet`, `eval_pair`, `eval_append`, `eval_var_last`, the atom
   equations, and the `syncOpOf` inversions.
6. The census by evaluation: `levelAt`, `performSites`, `performSites_complete`, `build_elaborates`.
7. The list algebra of an observation: `length_filter_zip_fst`, `length_filter_zip_snd`,
   `length_filter_le_of_imp`, `length_filter_add_le`, `all_of_length_filter`.

`cleans_once` (the other seat's goal in this file) shares items 1, 4 and 6. Every write site keeps a
list cell a prefix of its next value. The six note sites append one entry each, with their
request's number, and the other sites refuse a list (the census, read on two states). Its
multiplicity is the stages' "the finalizer noted" bit. So one `shop_stages` invariant with a
`cleaned` stage per request serves all four goals.
