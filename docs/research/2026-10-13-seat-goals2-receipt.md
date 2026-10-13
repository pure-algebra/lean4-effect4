# Seat GOALS-2 receipt: the writer debits and the log goals (2026-10-13)

Status: receipt (history, not authority). Seat GOALS-2, branch `seat/goals2`, worktree
`~/Dev/lean4-effect4-goals2`. The brief is `docs/research/2026-10-13-seat-goals2-brief.md`.

## The one thing to know before merging

`Atomic.cleans_once` is proved: `WriterHistory.evaluation` is a theorem in place, and
`Atomic.atomic` now rests only on `Atomic.Store.shop_stages` (measured). The two other goals of the
brief stay open and unchanged. `Workers.Assertions.logs_step` and
`QueueWorkers.Assertions.logs_history` need a whole-history answer-flow invariant of the frame
machine: each acquisition answers `nat i`, and each environment binds the `released` cell. No seat
has built it, and both Timeout goals need it too (§4). The branch also makes the source ledger and
the Atomic writer instances of one set of ledger-generic laws and deletes their duplicates. No
surviving statement changed, and no goal was weakened.

## Base, head and evidence words

- Base: `052e826df` on `refactor/phase1-phase3`. Head: the commit that adds this receipt; the last
  code commit is `a81e6450c`.
- Evidence words: **proved** means the kernel checked it, audited at `[propext, Quot.sound]`.
  **Tested** means a finite evaluation. **Assumed** means read in the source, not checked.
  **Measured** means a tool's output at this head.

## 1. The frontier before this session

`#plan_status` measured it at the base. The reader is a scratchpad file that imports the three
scenario modules and `ProofGraph.Plan`, run with `LEAN_NUM_THREADS=2 lake env lean`.

| Application claim | Goals it rests on (measured) |
| --- | --- |
| `Atomic.atomic` | `Atomic.Store.shop_stages`, `Atomic.WriterHistory.evaluation` |
| `Workers.workers` | `Workers.Assertions.logs_step` |
| `QueueWorkers.queueWorkers` | `QueueWorkers.Assertions.jobs_step`, `logs_history`, `rest_step` |

| Clause or goal | Standing (measured) |
| --- | --- |
| `Atomic.cleans_once` | modulo `Atomic.WriterHistory.evaluation` |
| `Workers.releases_once` | modulo `Workers.Assertions.logs_step` |
| `QueueWorkers.releases_once` | modulo `QueueWorkers.Assertions.logs_history` |
| the three goals of the brief | goal |

The tool reported six next goals for the three claims.

## 2. What landed, by slice

Seven commits on `seat/goals2`. Each table gives the state at the head.

### 2.1 Slice 1 (`0775cae53`): `WriterHistory.evaluation` proved

The action arms became generic in the weight. The new library module
`src/Effect4/Laws/Machine/WriterActions.lean` sits in namespace `Effect4.Machine.WriterWeights`,
beside `mask_bound` and `fork_bound`.

| Declaration (`WriterWeights`) | What it states | Standing |
| --- | --- | --- |
| `rows_bound` | an evaluation that keeps the stored rows owes only its acting frame's bound | proved |
| `answer_le`, `uninterruptible_frame`, `uninterruptible_le` | a zero-weight answer, masked or not, keeps the saved reservations | proved |
| `ActionInputs` | the instance's weights of the codes the arms install | structure |
| `Carried` | a fork or mask program within its producer's reservation; a close's installed code at zero; a parallel close excluded | definition |
| `fork_in_bound`, `countdown_plan_bound`, `link_plan_rows` | the scoped fork, the countdown registration, the scope-link plan | proved |
| `action_bound` | every `withFiber` arm keeps the other rows' reservations and spends the acting frame's | proved |

The Atomic writer's evaluator debit is the new module
`Test/Dogfood/Scenario/Atomic/WriterNative.lean`, which `WriterHistory` imports.

| Declaration (`WriterNative`) | What it states | Standing |
| --- | --- | --- |
| `Free`, `no_queue`, `events`, `control`, `terminal_zero` | the ledger's row facts, moved down from `WriterHistory` | proved |
| `restricted` | the built shop is sequential and race-free | proved |
| `debit_ledger`, `local_debit`, `rows_debit`, `emit_extends`, `pop_frame_le` | the writer debit as the ledger's `IterDebit`; a frame bound with a kept heap and an extended trace | proved |
| `action_inputs`, `close_zero`, `close_unsafe_zero`, `interp_close_zero` | every code an arm installs weighs zero for the writer | proved |
| `launched`, `mask_child_le`, `fork_child_le`, `launched_le`, `carried` | a fork or mask program of an owned thunk is a resolved child point within the thunk's reservation (`interp_source_children`, `scoped_fork_children`) | proved |
| `action_debit`, `async_cancel_zero`, `primitive_debit` | the action arm, and `PlaceFunding.PrimitiveInputs` for the writer | proved |
| `enter_scoped_debit`, `exit_scoped_debit` | scoped entry moves the reservation to its body; scoped exit installs zero-weight close code after the actual pop | proved |
| `native_debit`, `iteration_debit` | one native evaluation; one charged iteration with the forced yield | proved |

`exit_scoped_debit` reads the primitive fallback at the row table `[]`. The shop's table is `[]`
(`Atomic.Store.shop_table`), so the writer's frame lemmas, stated at `built.table`, apply. A
writer for a crew with rows needs those lemmas generic in the table.

### 2.2 Slice 2 (`ee9d3e755`): one action debit for every place ledger

The brief asks that `SourceOpportunityNative`'s per-arm debits become generic in the weight.
Slice 1 stated them generically; slice 2 makes both ledgers instances. The new module is
`src/Effect4/Laws/Program/PlaceFunding/Actions.lean`.

| Declaration | What it states | Standing |
| --- | --- | --- |
| `PlaceFunding.withFiber_administrative`, `countdown_administrative` | every native action, and a countdown registration, extends the trace by administrative events only | proved |
| `PlaceFunding.Events.trace_debit` | an administrative extension spends no more than it issues | proved |
| `PlaceFunding.action_debit` | the action arm of every place ledger whose fiber row reads a frame weight model | proved |
| `Opportunities.native_action_debit` | an instance, moved to `SourceOpportunityPrimitive`; statement unchanged, its race-freedom and distinct-id premises unread (`_raceFree`, `_unique`) | proved |
| `Opportunities.close_scope_zero` | the zero fact of the deleted `close_scope_debit` | proved |

### 2.3 Slice 3 (`2fab03f7f`): the release-writes control

`Test/Dogfood/Scenario/ReleaseWrites.lean` holds five `#guard` lines, reached through
`Workers.Assertions` (§4.1). `logs_step`'s docstring names the control; its statement is unchanged.

### 2.4 Slice 4 (`8f503a571`): the source ledger is an instance of `PlaceFunding.Local`

| Declaration | What it states | Standing |
| --- | --- | --- |
| `Opportunities.source_local` | the source ledger's `PlaceFunding.Local` facts | proved |
| `Opportunities.decision_budget` | statement unchanged; now `Local.decision_lift` with `Lift.stepDecisionState_lift` | proved |
| `Opportunities.history_budget` | statement unchanged; now `Local.history_funded` | proved |
| `source_stores`, `source_administration`, `source_inputs` | made public for `source_local` | proved |

### 2.5 Slice 5 (`96fd1b12e`): one charged iteration and one installation for every place ledger

The new module is `src/Effect4/Laws/Program/PlaceFunding/Native.lean`.

| Declaration | What it states | Standing |
| --- | --- | --- |
| `PlaceFunding.debit_prefix` | a prefix that keeps rows and store, extends the trace administratively and lowers the acting fiber composes with the debit after it | proved |
| `PlaceFunding.iteration_debit` | the loop top, the op count and the forced yield, from the ledger's native debit | proved |
| `PlaceFunding.Evaluation.of_debits` | the evaluator obligation from the native and iteration debits, each installed once | proved |
| `Opportunities.iteration_debit`, `source_evaluation` | instances; statements unchanged; `source_evaluation` made public | proved |
| `WriterNative.iteration_debit`, `WriterHistory.evaluation` | instances; the statement and placement of `evaluation` unchanged | proved |

### 2.6 Slices 6 and 7 (`4e0ea9ada`, `a81e6450c`): one countdown debit; docstrings

`PlaceFunding.bound_debit` is the shared core of `action_debit` and the new
`PlaceFunding.countdown_debit` (with `countdown_state`). Both ledgers' primitive countdown inputs
are its instances. `Opportunities.source_action_inputs` factors the source's installed-code
weights. Slice 7 corrects the consumers that `PlaceFunding.Run`'s docstrings name.

### 2.7 Deleted

Each deleted declaration had no user left, measured with `grep` over `src`, `Test` and `tools`.

| Module | Deleted | Why |
| --- | --- | --- |
| `SourceOpportunityNative` | `replace_current_debit`, `mask_debit`, `spawn_outside_le`, `fork_debit`, `fork_in_debit`, `fork_scoped_debit`, `interrupt_as_debit`, `close_scope_debit`, `interpreted_fork_debit`, `interpreted_fork_in_debit`, `link_plan_debit`, `countdown_plan_debit` | superseded by the generic arms |
| `SourceOpportunityNative` | `outside_emit`, `outside_update_le`, `outside_edits_le` | their last consumers were superseded |
| `SourceOpportunityNative` | `outside_modify_le`, `interrupt_record_le`, `countdown_debit`, `drop_outside`, `link_debit` | no user at the base (measured, `git grep` at `052e826df`) |
| `SourceOpportunityHistory`, `SourceOpportunityCommands` | `budget_decision_lift`; `command_debit`, `source_zero_allowance`, `source_installed` | superseded by `PlaceFunding.Local` and `Evaluation.of_debits` |
| `SourceOpportunityExecution` | `loop_top_frame_le` | superseded by `PlaceFunding.iteration_debit` |
| `Atomic/WriterMachine` | `action_debit`, `mask_debit`, `fork_debit` | superseded by `PlaceFunding.action_debit` |
| `Atomic/WriterNative` | `debit_prefix`, `loop_top_le`, `yield_frame`, `countdown_debit` (all from slice 1) | superseded in slices 5 and 6 |
| `Scenario/SourceOpportunity` | `workers_native_fork_in_debit` | dead, and its lemma was deleted |

`SourceOpportunityNative` now holds `Debit` and `close_scope_zero`.

## 3. Placements (AGENTS.md, Trust)

Every landed theorem serves the concept `scope-lifetime-finalization` and requirement R11, "at most
once per registration, counted by identity" (`docs/core/system-map.md` §8). The iteration laws
serve `reactive-scheduling` too. Each docstring names its consumer.

| Theorem (group) | Question and consumer | Reach | What it does not establish | Unlock |
| --- | --- | --- | --- | --- |
| `WriterHistory.evaluation` (the planned goal, now proved) | `PlaceFunding.Evaluation` for the writer; consumer `local_facts`, then `history_funded`, `Cleanup.log_debits`, `cleaned`, `cleans_once` | the built shop, every request identity, every machine with distinct fiber ids and source ownership, every fiber and latch | finalizer progress, release order, a host observation | `Atomic.cleans_once` proved |
| `WriterNative.*` | the native and iteration debits, steps of `evaluation` | as `evaluation` | the same | as `evaluation` |
| `WriterWeights.action_bound` and its helpers | the action arm, a step of `PlaceFunding.action_debit` | every frame weight model, interpreter, machine, fiber, latch and action but a parallel close | a store, trace or race bound; source ownership | no per-weight copy of the arms |
| `PlaceFunding.action_debit`, `countdown_debit`, `bound_debit`, `withFiber_administrative`, `Events.trace_debit` | the action and countdown arms of `PlaceFunding.Evaluation`; consumers the source ledger's and the writer's primitive debits | a ledger with no queued weight, administrative events spending no more than they issue, a frame-model row, a kept store | progress, host agreement | a future writer owes no action or countdown arm |
| `PlaceFunding.iteration_debit`, `debit_prefix`, `Evaluation.of_debits` | the two fields of `PlaceFunding.Evaluation`; consumers `source_evaluation`, `Opportunities.iteration_debit`, `WriterNative.iteration_debit`, `WriterHistory.evaluation` | every program, row table, machine with source ownership, owned fiber and latch | the native debit itself, which each instance supplies | a future ledger owes only its native debit |
| `Opportunities.source_local`, `decision_budget`, `history_budget` | the source ledger's history step; consumers `FinalizerRun.census_pushes_once` and the scenario source bounds | unchanged from the base | unchanged from the base | one history law for both ledgers |
| `ReleaseWrites.readsSlot` guards (a control) | why `logs_step` and `logs_history` need a value premise | the two built crews at total 2 | any machine property | the finding of §4 |

## 4. Workers and QueueWorkers: the log goals need a value invariant

Neither `Workers.Assertions.logs_step` nor `QueueWorkers.Assertions.logs_history` closes on this
branch. Their writer ledger cannot be funded by `PlaceFunding.Local`, whose local facts quantify
over every machine with source ownership (`ConfigurationAt`).

### 4.1 Why

- **The release note writes the acquired value from its environment** (tested, a finite
  evaluation, `Test/Dogfood/Scenario/ReleaseWrites.lean`). Under each member's acquisition in both
  built crews, the acquisition note appends the member's literal `nat i`. The release note appends
  `nat 7` when every bound slot holds `nat 7`: it reads the bound acquired value. The Atomic writer
  instead reads each note's literal identity from a source census (`WriterSource.bounded_census`).
- **The count clause is per acquisition path** (`releaseAt (acquirePath i)`). It holds only because
  acquisition `i` answers `nat i` (assumed). The crews' acquisition is
  `andThen (note opened (nat id)) (succeed (nat id))`. The callback `.acquired p ctx s` of
  `Program/Compile.lean`'s `contAOf` appends the answer to the capture's environment.
- **The heap weight must single out the `released` cell** (assumed, reading the crews). The `opened`
  cell also receives `nat 1` and `nat 2`, and the count cell holds naturals. A note's cell is the
  value of its cell variable, which the root's `Ref.make` answers bind.
- `ConfigurationAt` fixes source paths and lexical lengths, not environment values (assumed,
  reading `NativeConfiguration.lean` and `NativeScope.lean`). A machine with source ownership may
  hold the `opened` note with its cell variable bound to cell 1. One evaluation then appends
  `nat 1` to the log with no release start. So no local fact over `ConfigurationAt` machines funds
  the log clause (assumed; no kernel-checked counterexample).

### 4.2 What exists and what is missing

- The frame-level answer typing exists: `Machine.AnswerFlow` and eight companion modules, about
  1600 lines. They hold `SavedAt`, `StackAt`, `ResultAt`, `FrameAt`, and the pop, push, hook,
  cause-pop and action laws. Their headers name `Workers.Assertions.logs_step` among their
  questions. Each says that no source, allocation or command premise of it is supplied (assumed,
  reading).
- The Timeout instance (`Test/Dogfood/Proofs/HostTimeoutNumberFlow.lean`,
  `HostTimeoutNumberCounted.lean`) builds a numeric answer-flow assertion and stops short of a
  whole-history producer too (assumed, reading).
- Missing for four goals (`Workers.logs_step`, `QueueWorkers.logs_history`, `Timeout.cleanup_keeps`,
  `Timeout.retries_declared`): **a whole-history producer of answer flow**. For answer classes, it
  is the analogue of `decision_lift_at` (source ownership) and of
  `PlaceFunding.Local.history_funded` (place ledgers). The `Native*` modules behind
  `decision_lift_at` hold about 4250 lines (measured with `wc`).

### 4.3 The route this seat recommends (a proposal; no goal planted)

1. The producer, stated once as a `Lift.DecisionLift` that keeps
   `ConfigurationAt root m ∧ ∀ f ∈ m.fibers, AnswerFlow.FrameAt model interp (worldOf m) (outputOf f) f.frame`.
   Its local facts are the per-arm answer-class transports (existing) and each fiber's own
   evaluation, the fork's child, the edits and the commands (missing). It is the previous seat's
   proposed `FiberLocal` law (`2026-10-13-seat-goals-receipt.md`, §5.1) at the answer-class level.
2. The crews' instance, as answer classes of the saved callbacks. The root's five allocation
   answers are cells 0 to 3 and the gate; each acquisition answers `nat i`.
3. `PlaceFunding.Local` generalized to a machine invariant `Q` that a decision lift carries:
   `Evaluation L (ConfigurationAt root ∧ Q)`, with `history_funded` otherwise unchanged.
4. Each crew's writer ledger: the `released` cell's count of `nat i`, reservations by acquisition
   path, credits by `releaseAt`. Its evaluator debit reuses `PlaceFunding.action_debit`,
   `countdown_debit`, `iteration_debit` and `Evaluation.of_debits`. Its frame lemmas must be generic
   in the row table, since both crews declare rows.

Options for the owner (a choice of route and size, not a question of meaning):

- (a) Build the whole-history answer-flow producer (recommended). It serves four goals.
- (b) Carry the reference machine's typed state (`Typed/Assembly.lean`) to the frame machine.
  Whether its types fix `nat i`, and whether an agreement covers forks, rows and scopes, is
  unchecked.
- (c) Restate the log clause per captured value. Not recommended: the read (`log` is `Nodup`) still
  needs the acquired value, since release custody counts by path.

## 5. Commands and results

All with `LEAN_NUM_THREADS=2`, one `lake` at a time, in `~/Dev/lean4-effect4-goals2`.

| Command | Result (measured) |
| --- | --- |
| `git worktree add … -b seat/goals2 refactor/phase1-phase3`; `cp -c -R .lake …` | the copy took 37 s |
| `lake build Test.Dogfood.Scenario.{Workers,QueueWorkers,Atomic} ProofGraph.Plan` | passed, 1263 jobs, all restored from the cache |
| `lake env lean <scratchpad>/Frontier.lean` | the frontier of §1 |
| `lake env lean src/Effect4/Laws/Machine/WriterActions.lean` | passed after two repairs (an unused instance, then `omit` before the docstring) |
| `lake build Effect4.Laws.Machine.WriterActions` | passed, 221 jobs |
| `lake env lean Test/Dogfood/Scenario/Atomic/WriterNative.lean` | passed after three repairs (a zero sum, a redundant `rfl`, a machine unified too early) |
| `lake build Test.Dogfood.Scenario.Atomic.WriterNative` | passed, 1168 jobs |
| `lake build Effect4.Laws Test.Dogfood.Scenario.Atomic` (slice 1) | passed, 1507 jobs; the scenario's `#scenario_gate` ran |
| `lake env lean src/Effect4/Laws/Program/PlaceFunding/Actions.lean` | passed after one repair (the event list, and eta-different atoms) |
| `lake build Effect4.Laws Test.Dogfood.Scenario.{Atomic,Workers,QueueWorkers}` (slices 2, 4, 5, 6, 7) | passed: 1519, 1521, 1518, 1520 and 1516 jobs, no warning |
| `lake env lean <scratchpad>/ReleaseSites.lean`, `QueueReleaseSites.lean` | the probes of §4.1 |
| `lake build Test.Dogfood.Scenario.ReleaseWrites Test.Dogfood.Scenario.Workers` | passed, 1229 jobs |
| `lake build Test.Audit.ProofStyle` | fails with 176 findings, none in a file this branch changes (measured per file); 170 are stale baseline entries |
| `lake build Test.Audit.TraversalCensus` | fails in `Test/Audit/ExhaustiveFixture.lean` and `TraversalFixture.lean`: "Missing cases" for `Ty.contextOf`; both import only `Effect4`, unchanged here |
| `lake env lean <scratchpad>/ModuloCheck.lean` | the attributions of §6 |
| `lake env lean <scratchpad>/AuditHead.lean` | §6 |
| `lake env lean <scratchpad>/Frontier.lean`, at the head | §7 |
| `python3 scripts/check-language.py --show` on this receipt | no finding |

## 6. Axiom output

`#axiom_audit` (`tools/ProofGraph/AxiomAudit.lean`), from scratchpad files run with `lake env lean`.

| Modules | Output (verbatim) |
| --- | --- |
| slice 1: `WriterActions`, `WriterNative`, `WriterHistory`, `Cleanup`, `Test.Dogfood.Scenario.Atomic` | `208 declarations within [propext, Quot.sound], 3 of them modulo planned goals; 0 planned goals` |
| slice 2: `WriterActions`, `PlaceFunding.Actions`, `SourceOpportunityNative`, `SourceOpportunityPrimitive`, `Scenario.SourceOpportunity`, `WriterMachine`, `WriterNative`, `WriterHistory` | `440 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals` |
| the head: the seventeen modules this branch changes, from `WriterActions` to `Workers.Assertions` | `569 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 1 planned goals` |

At the head, the one planned goal is `Workers.Assertions.logs_step`. The two declarations modulo it
are its assemblies `step` and `history` (measured with `#plan_status`). In slice 1, the three
modulo planned goals are `Atomic.atomic`, `counted` and `committed`. They rest on
`Atomic.Store.shop_stages`, outside the audited modules (measured).

## 7. The frontier after this session

Measured with the same reader at the head.

| Application claim | Goals it rests on (measured) |
| --- | --- |
| `Atomic.atomic` | `Atomic.Store.shop_stages` |
| `Workers.workers` | `Workers.Assertions.logs_step` |
| `QueueWorkers.queueWorkers` | `QueueWorkers.Assertions.jobs_step`, `logs_history`, `rest_step` |

| Clause or goal | Standing (measured) |
| --- | --- |
| `Atomic.cleans_once` | proved |
| `Atomic.WriterHistory.evaluation` | proved |
| `Workers.releases_once` | modulo `Workers.Assertions.logs_step` |
| `QueueWorkers.releases_once` | modulo `QueueWorkers.Assertions.logs_history` |

The tool reports five next goals for the three claims (six before).

## 8. Open obligations, proposals and merge-time edits

Open obligations, in the order this seat recommends:

1. The whole-history answer-flow producer and the crews' instance (§4.3, items 1 and 2).
2. `PlaceFunding.Local` over a carried invariant, then the Workers and QueueWorkers writer ledgers
   (§4.3, items 3 and 4), with frame lemmas generic in the row table.
3. The remaining frontier goals of the previous receipt, unchanged here: `Run.CallTree.request_leads`,
   `Atomic.Store.shop_stages`, `QueueWorkers.jobs_step` and `rest_step`, both Timeout goals, and
   `FinalizerRun.once_placed_outside_census`.
4. A clean-up: `Opportunities.native_action_debit` no longer reads its race-freedom and distinct-id
   premises, so the `unique` premise of `primitive_debit`, `native_debit`, `iteration_debit` and
   `loop_command_debit` is unread too. Dropping it strengthens those statements and touches their
   callers.

Proposed for the coordinator (no register edited here):

- The registry claim `place-ledger-history` (the previous seat's proposal), pointer
  `PlaceFunding.Local.history_funded`, role preservation. It now has two instances: the Atomic
  writer and the source ledger.
- A registry claim for the answer-flow producer, role preservation, concept `reactive-scheduling`
  with `store-typing` R4; consumers the four goals of §4.2.

Outside this seat's edit scope, at the merge:

- Regenerate `generated/semantics.md` (`make gen-semantics`): `WriterHistory.evaluation` and
  `Atomic.cleans_once` are proved.
- `docs/core/system-map.md` §8 and `docs/STATE.md` item 00 name `WriterHistory.evaluation` as open.
- `Test.Audit.ProofStyle`, which `Test/All.lean` imports, fails at this head with findings only in
  files this branch does not change; its baseline needs `#proof_style_record`. The same failure is
  expected at the base (assumed: the scanned files are unchanged; not rebuilt at the base).
- `Test.Audit.TraversalCensus` fails in two fixtures that miss `Ty.contextOf`; the fixtures import
  only `Effect4`, which this branch does not change.

## 9. Files changed

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Machine/WriterActions.lean` | new: the action arms, generic in the weight |
| `src/Effect4/Laws/Program/PlaceFunding/Actions.lean` | new: the action and countdown arms of every place ledger |
| `src/Effect4/Laws/Program/PlaceFunding/Native.lean` | new: the charged iteration and `Evaluation.of_debits` |
| `src/Effect4/Laws/Program/PlaceFunding/History.lean`, `PlaceFunding/Run.lean` | docstrings: their consumers |
| `src/Effect4/Laws/Program/SourceOpportunityNative.lean` | now `Debit` and `close_scope_zero` |
| `src/Effect4/Laws/Program/SourceOpportunityPrimitive.lean` | `native_action_debit` and `source_action_inputs`; the countdown input as an instance |
| `src/Effect4/Laws/Program/SourceOpportunityExecution.lean` | `iteration_debit` as an instance |
| `src/Effect4/Laws/Program/SourceOpportunityCommands.lean` | `source_evaluation` as an instance; source facts public |
| `src/Effect4/Laws/Program/SourceOpportunityHistory.lean` | `source_local`; the budget lemmas through `PlaceFunding.Local` |
| `src/Effect4/Laws.lean` | one import at the end |
| `Test/Dogfood/Scenario/Atomic/WriterNative.lean` | new: the writer's evaluator debit |
| `Test/Dogfood/Scenario/Atomic/WriterHistory.lean` | `evaluation` proved in place; row facts moved to `WriterNative` |
| `Test/Dogfood/Scenario/Atomic/WriterMachine.lean` | superseded action debits deleted |
| `Test/Dogfood/Scenario/Atomic/Cleanup.lean` | docstring: `evaluation` is no longer a goal |
| `Test/Dogfood/Scenario/SourceOpportunity.lean` | a dead instance deleted |
| `Test/Dogfood/Scenario/ReleaseWrites.lean` | new: the control of §4.1 |
| `Test/Dogfood/Scenario/Workers/Assertions.lean` | imports the control; `logs_step`'s docstring names it |
| `docs/research/2026-10-13-seat-goals2-receipt.md` | this receipt (force-added) |

Bounded or host-only evidence: the five `ReleaseWrites` guards are finite evaluations of two built
programs at total 2 (tested). Everything else landed is proved. No host run.
