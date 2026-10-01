# Seat I receipt: seat C's split integrated with seats B, E and F

Seat I of the 2026-10-01 landing. Brief: `docs/research/2026-10-01-landing/brief-I.md` (main
checkout); plan: `plan.md` there (§4 rules, §5 measure). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-I`, branch `seat/I`. Evidence words: **proved** (a kernel
theorem compiled here, axioms printed), **reproduced** (another seat's proved fact compiled again
here), **tested** (a finite check run here: a build's report, a `#guard`, a `grep`, a prototype
build), **assumed** (not run here; a reading names the lines read). Every number below comes from a
command named beside it; the build logs are in this seat's scratchpad and every count was taken
from them with `grep -c` or the ledger script named in "The ledger".

## The one thing first

The union builds green with both gates (`LEAN_NUM_THREADS=6 lake build Effect4.Laws Test.All`,
exit 0, 734 jobs; tested). Seat B's and seat C's statements are kept or strengthened, the controls
the merge flips are kept as history over their old definitions beside proved positive controls,
and one statement is weakened because the brief's own hunk makes it false
(`ProtocolPosts.CloseScope.close_code_typed`, now at a world whose store holds the scope; its old
form is refuted by `close_code_refused_absent`, proved). **The one thing: repair 5 does not repair
`M6Ledger.step_deliver`.** Seat C's hunk on `fiberPre` landed as written, but
`M6Capstone.H1HaltAmendment.step_deliver_refuted_by_absent_scope` still compiles at head (proved,
`[propext, Quot.sound]`): `TypedProg` types the scope-exit marker through its own `scopeExit`
constructor, which reads no pre (the `fiber` arm excludes the marker by `notScopeExit`), so the
hunk's `scopeExit` arm binds only the generic protocol judgment over `Ψ_F`. The repair is a
scope-liveness premise on that constructor. A reverted prototype measured it (tested): besides the
premise, one line each in `Residual.lean`'s `fiber_inv` and `typedProg_mono`, seat E's
`Seq.close_typed` and seat C's `RawOrderLoad`; the repaired form `∀ w, ¬ ConfigTyped … machine
(command :: rest)` elaborates; and eight `H1HaltAmendment` controls that type the absent-scope
callback become false and could stay only as history over a copy of the judgment without the
premise. That is not a few lines, so by the brief's rule I stopped there and left the control red;
a decisions row is proposed. Also before merging: `M6Stack` is deleted in favour of `M3bWorld`
(row 87), and `E4-TYPED-CE-010` is flipped: M5's proposition over `J` holds at the corpus's
`awaitFiber.value` (proved).

## Base and head

Base: `af3799f9` (`refactor/phase1-phase3`, seats E, F and B merged) with `seat/C` at `45281aed`
merged textually by the coordinator as `3361bc3d`. Commits on `seat/I`, in order:

| Commit | Repair |
| --- | --- |
| `60bc5d69` | 1: the worker's saved frame in `M6Capstone` under the closed frame arms |
| `4a08dd1b` | 2: seat B's frame battery under row 134's split |
| `cd9a51bf` | 3: `E4-TYPED-CE-010` flipped against M5 over `J` |
| `6a477f47` | 4: one owner for world monotonicity, `M3bWorld` |
| `509d243c` | 5: row 139's premises on the halting fiber rows (control left red) |
| `9247d623` | 6: `storeTyped_of_typedState` |
| head | this receipt (the commit that adds this file; its hash is in the handback) |

Repairs 7 and 8 needed no source change. No push. `git diff --stat 3361bc3d..9247d623`: 7 files
changed, 535 insertions, 164 deletions (tested).

## Every changed path

| Path | Repairs | Change |
| --- | --- | --- |
| `src/Effect4/Laws/Program/Typed/Residual.lean` | 4, 5 | `fiberPre`'s halting arms (seat C's hunk); `fiberPre_mono`'s arms; the `M3bWorld` report moved out (comment at `:751`) |
| `src/Effect4/Laws/Program/Typed/Assembly.lean` | 3, 4, 5, 6 | `preds_savedOk_mono` and its `M3bWorld` goal; `M6Stack` and its stand-ins deleted; the `M3bWorld` audit and report at the foot; `storeTyped_of_typedState`; docstrings of `MachineLive`, `step_loop`, `step_deliver`, `typedState_reachable` and the module header |
| `Test/Counterexamples/Machine/Semantics/M6Capstone.lean` | 1, 5 | `worker_saved`'s binders; four refusal controls in `Liveness`; `step_deliver_refuted_by_absent_scope`'s docstring |
| `Test/Program/FramesNotKripke.lean` | 2, 4 | the split's shapes; `good_config`, `afterGood_config`; `step_loop_good` over `I`; `preds_savedOk_mono` a one-line use |
| `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean` | 3 | history over seat B's `OldTypedProg`; the flip `code_typed`, `loadsTyped`, `capstone_at_load`; one `#guard_msgs (error)` fixture |
| `Test/Program/ProtocolPosts.lean` | 5 | `close_code_typed` at a live scope; `close_code_refused_absent`, `close_code_typed_live` |
| `Test/Program/TypedSplit.lean` | 4, 6 | `#print`/`#print axioms` lines follow the deleted and added theorems |
| `docs/research/2026-10-01-landing/receipt-I.md` (new, force-added) | — | this receipt |

Not touched: `Test/All.lean` (no battery added), `Test/Audit/AxiomGate.lean`, `lakefile.toml`, the
root imports, and every coordinator file (`docs/core/decisions.md`, `docs/STATE.md`, `README.md`,
`AGENTS.md`, `docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md`).

## Commands and results

- At the merge `3361bc3d`: `LEAN_NUM_THREADS=6 lake build Effect4.Laws.Program.Typed.Assembly`,
  exit 0, 382 jobs, 8 min 10 s (seat C's `Typed/Sources.lean` sits under `World.lean`, so the
  typed-state chain recompiled). Then the 20 test modules that import the typed state in one lake
  call: three failed, each where a receipt foresaw it (`M6Capstone.lean:1889`,
  `FramesNotKripke.lean`, `AwaitLoad.lean:98`); the rest built unchanged (tested).
- Narrow builds per repair (all `LEAN_NUM_THREADS=6 lake build …`, exit 0 at each commit): repair 1
  `Test.Counterexamples.Machine.Semantics.M6Capstone`; repair 2 `Test.Program.FramesNotKripke`;
  repair 3 `Effect4.Laws.Program.Typed.Assembly Test.Counterexamples.Machine.Semantics.AwaitLoad`;
  repair 4 `Assembly`, `Seq` and the 14 direct importers of `Residual` and `Assembly` (402 jobs);
  repair 5 `Effect4.Laws.Program.Typed.Residual`, then the 24-target consumer build (failed only at
  `ProtocolPosts.lean:455`, the theorem the hunk makes false), then `Test.Program.ProtocolPosts
  Test.Counterexamples.Machine.Semantics.AwaitLoad` and `…M6Capstone`; repair 6 `Assembly
  Test.Program.TypedSplit` and the 11 direct importers of `Assembly`. Batteries also checked by
  `LEAN_NUM_THREADS=6 lake env lean -DwarningAsError=true <file>` while editing (`AwaitLoad`).
- **Final:** `LEAN_NUM_THREADS=6 lake build Effect4.Laws Test.All` at `9247d623`: exit 0, "Build
  completed successfully (734 jobs)", 4 min 40 s wall. Gates, as printed: "Effect4 library-root gate:
  134 API/utility modules, 220 Laws-only modules; every library source is reachable; Effect4 never
  reaches Laws" and "Effect4 module and axiom gate: checked 516 modules and 70807 declarations;
  semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (15 module(s), 23
  declaration(s)) additionally allows Classical.choice". `grep -c sorryAx` on the final log: 0.
- Axioms: a scratch file of `#print axioms` for every theorem added or re-proved (40 names, listed
  per repair below), run by `lake env lean` after the final build: 40 lines, all `[propext,
  Quot.sound]`, none with `sorryAx` or `Classical.choice` (tested). Axiom lines per battery in the
  final log (`grep -c`): `FramesNotKripke` 19, `ProtocolPosts` 46, `AwaitLoad` 14, `M6Capstone` 127,
  `TypedSplit` 71, `StaleCode` 68, `RawOrderLoad` 5.
- `make check-cases`: not run. No match added here is on a policy family (`cases-policy.json`:
  `Ty`, `Eff`, `NativeOp`, `RowKind`, `RowShape`, `Registration`, `Lit`, `Term`, `CauseTerm`); the
  new case splits are on `Expect`, `ScopeState`, `FiberOp` (in `fiberPre_mono`) and `Val`. No `Ty`
  case analysis (row 132): `AwaitLoad.sub_exitOf_mono` rewrites with the generated arm lemma
  `Ty.sub_args_exitOf`, as `TypeAlgebra.sub_prod_mono` does, and `fiber_of_fits` splits the value
  under `Fits` at the fixed constructor `.fiberOf`, as `Membership.fits_fst` does. No generator run.
  No `simp_all`, `first`, `try` added under `src/`; hand `simp` is `simp only […]`.

## Per repair

### 1. `M6Capstone.lean` under seat C's restated sections (`60bc5d69`)

Seat B's three-lambda hunk had been applied by the merge (`saved_typed` in `H1TerminalAmendment`,
`typed` and `old_typed` in `H1HaltAmendment`) and elaborates (tested). The one failure was seat C's
own `H1HaltAmendment.worker_saved` (`M6Capstone.lean:1885`), written against the one-world arms:
its `resume` frame now takes the closed binders (`fun w' _ ex _ _ => callback_typed w' ex`,
`fun _ _ _ typed _ => typed`). Statement unchanged; `[propext, Quot.sound]`. No control flipped.

### 2. Seat B's batteries under the split (`4a08dd1b`)

`Test/Program/FramesNotKripke.lean`, all `[propext, Quot.sound]`:

| Theorem | Line | Change |
| --- | --- | --- |
| `typed_of` | `:376` | `TypedState` without the queue argument (the unused `commands` parameter dropped); `savedPosition_of_saved` at its five arguments (no machine, queue or position) |
| `queue_of`, `afterGood_queueOk` | `:456`, `:880` | `QueueOk.links`, vacuous on queues with no `link` |
| `good_typed`, `afterGood_typed` | `:630`, `:779` | `TypedState` without the queue argument |
| `good_saved`, `afterGood_saved` | `:626`, `:770` | new: the root's frame, code included |
| `good_config`, `afterGood_config` | `:639`, `:917` | new: the green control's input and output in `I` (`ConfigTyped`) |
| `step_loop_good` | `:950` | restated over `ConfigTyped` (a strengthening: seat B's queue-relative `TypedState … afterGood.2` typed the root's current code, which is `ReadCode`'s under the split, and `ConfigTyped` also carries `QueueOk`) |
| `preds_savedOk_mono` | `:1038` | re-proved for the split's bundle (its `SavedOk` is the stack and the provenance) by `Contracts.stackAccepts_mono`; repair 4 made it a one-line use |

`typed_of`, `good_typed` and `afterGood_typed` state the split's `TypedState`, which no longer
carries the current-code clause (seat C's restatement, row 134); the code they carried before is in
`good_config`, `afterGood_config` and `step_loop_good`, so no claim of seat B's battery is lost.

Controls: the historical ones (`stackAccepts_not_mono` `:238`, `step_loop_refuted` `:565`,
`hookLawsX_old`, `output_typed_one_world`, the historical control `evaluate_keeps` `:604`) compile
against the union over `Old.*`, which reads the current `QueueOk` (now with `links`); the positive
ones (`step_loop_good`, `good_config`, `afterGood_config`, `good_stack_transports`,
`bad_not_kripke_initial`, `bad_not_kripke_by_transport`, `hookLawsX_refused`, `frameAccepts_now`,
`stackAccepts_now`) and the red `output_not_kripke` hold; the `#guard_msgs (error)` fixture is
unchanged. `ProtocolPosts.lean` needed no edit for the split: its historical `oldStatePreds`
extends `preds root`, so it inherits `ScopeExitOk`. The brief's "closed-exit arm": the generated
`StoresOk` (printed) holds each scope entry's `ScopeStateOk` in `c3`, whose `closed` arm is
`ScopeExitOk`; these batteries' machines hold no scope entry, so the arm is vacuous, and the
trailing `trivial` in their constructions is `StoresOk.c5 : True` (the still refused
`Stores.externals`). Every `Preds` value in the tree carries `ScopeExitOk`: `preds` (seat C),
`ValueMembership`'s and `TypedStateDecl`'s explicit instances (seat C), and the rest extend
`preds root` (tested: `grep` and the final build).

### 3. `E4-TYPED-CE-010` flipped (`cd9a51bf`)

`Test/Counterexamples/Machine/Semantics/AwaitLoad.lean` now imports `Typed.Seq` and
`Test.Program.ProtocolPosts`. All `[propext, Quot.sound]`.

- History (red, over the pre-row-136 judgment): `root_code_refused` (`:92`) is seat B's proof
  (`Test.Program.ProtocolPosts.AwaitLoad.root_code_refused`, over `OldTypedProg`) under seat C's
  name; `OldLiveCode` (`:97`), `OldMachineTyped` (`:103`), `OldLoadsTyped` (`:110`),
  `OldReachableTyped` (`:115`) are `J`, M5's and the capstone's propositions with `J`'s code
  clause read over `OldTypedProg` (every other clause current: the old omission, not a complete
  pre-amendment model); `loadsTyped_false` (`:122`) and `capstone_false` (`:143`) refute them.
  The fixture at `:165` pins seat C's refutation script failing against the current judgment
  (`#guard_msgs (error)`, the error at `⟨here, trivial⟩`).
- The flip (positive, current judgment): `sub_exitOf_mono` (`:196`), `fiber_of_fits` (`:203`),
  `fork_typed` (`:215`), `await_typed` (`:234`), `code_typed` (`:274`: the loaded root of
  `awaitFiber.value` typed at `pure (exitOf nat never)` at every world, by seat E's `seq_typed`
  for `denoteR`'s bind, the fork's post, the row-136 await post for a running target and
  `await_fits` for a target completed when the continuation is constructed), `loadsTyped` (`:285`:
  `LoadsTyped awaitProg rootTy 5 5`, by `machineTyped_load`), `capstone_at_load` (`:289`).
- The brief named seat B's `await_code_typed`; it is the instance at target `⟨1⟩` declared at
  `pure nat` and not completed. `machineTyped_load` needs the root's code at every world, so the
  await had to be typed at every handle the fork may answer and every completed-exit view:
  `await_typed` is that general form, by the same post.
- Statements: seat C's `root_code_refused`, `loadsTyped_false` and `capstone_false` read the
  current judgment and are false now (their negations are proved: `code_typed`, `loadsTyped`,
  `capstone_at_load`; the fixture pins the first's script failing); they are kept as history over
  the old judgment, as the brief asks. `Assembly.lean`'s capstone docstring
  (`:1474`) lists `E4-TYPED-CE-009` alone as live.

### 4. `M6Stack` against `M3bWorld` (`6a477f47`): delete `M6Stack`

Chosen: the brief's second option. `M6Stack.stackAccepts_mono` (`StackMono root`) and
`.savedOk_mono` (`SavedMono root`) stated seat B's `M3bWorld.stackAccepts_mono` and `.savedOk_mono`
again with the quantifiers moved; closing them through adapters would keep two statements of one
fact in two scopes, which the brief forbids. Row 87's formal-pass line puts "the monotonicity of
every owner predicate of `preds`" in `M3bWorld`, and seat C's own text made `M6Stack` a stand-in
"until seat B's `M3bWorld` closes it".

- Added: `preds_savedOk_mono` (`Assembly.lean:956`, proof moved from the battery,
  `[propext, Quot.sound]`); the goal `M3bWorld.preds_savedOk_mono` (`:1558`), closed by
  `#obligation_proved` (`:1616`, `.checked` at `[propext, Quot.sound]`); `M3bWorld`'s
  `#obligation_audit` and `#typed_state_obligations` moved from `Residual.lean` to
  `Assembly.lean:1618-1619`, so the scope is reported once, after its last goal.
- Deleted (seat C's, no other reader): `StackMono`, `SavedMono`, `savedMono_of_stackMono`, the
  three `M6Stack` goals and their report. Their content stays proved as `Contracts.stackAccepts_mono`
  and `Typed.savedOk_mono` (seat B) and `preds_savedOk_mono`.
- `FramesNotKripke.preds_savedOk_mono` (`:1038`) is a one-line use of the `src` theorem;
  `TypedSplit.lean` prints the new names; `M6Ledger.step_loop`'s docstring names `E4-TYPED-CE-012`'s
  repair (`step_loop_refuted` historical, `step_loop_good` over `I`).
- Reports (final log): `M3bWorld: 0 open, 6 proved, 6 total; ceiling 0`; audit "5 paired, 1 without
  a namesake, 0 mismatches".

### 5. `fiberPre`'s halting arms (`509d243c`): landed, control left red

- `Residual.lean`: `fiberPre` (`:144`) carries seat C's hunk verbatim: `interruptAs` a declared
  target, `runIn` a declared target and a live scope, `forkIn`, `closeScope` and `scopeExit` a live
  scope, `raceRegister` refused (with a comment naming the halting sites). `fiberPre_mono`
  (`:613`) re-proved for those arms (`isSome_extends` on `Γ`, scope persistence
  `ord.1.1.2.2.2.1`, `False.elim`); `typedProg_mono` and `savedOk_mono` re-checked; all
  `[propext, Quot.sound]`.
- Consumers: only `ProtocolPosts.CloseScope.close_code_typed` read an arm (`trivial` for the
  close-scope pre at every world). The hunk makes that statement false where scope 0 is absent
  (proved: `close_code_refused_absent`, `:463`, at the initial world), so it is restated with
  `(live : (w.state.scopes.entryAt 0).isSome = true)` (`:455`); `close_code_typed_live` (`:472`) is
  the positive instance over `StoreUnit.oneScope`. Seat B's `Adequacy` frame instances destructure
  `fiber_inv` and ignore the pre; `closeWalk_typed` reads rows the hunk leaves `True`.
- New controls, `M6Capstone.lean`, section `Liveness`: `interruptAs_unknown_refused` (`:2435`),
  `runIn_absent_refused` (`:2443`), `forkIn_absent_refused` (`:2451`), `raceRegister_refused`
  (`:2460`): typed code is refused at each arm's absent target or scope; all `[propext, Quot.sound]`.
- **Left red:** `H1HaltAmendment.step_deliver_refuted_by_absent_scope` (`M6Capstone.lean:2375`) still
  compiles (proved, `[propext, Quot.sound]`): `callback_typed` is built with `TypedProg.scopeExit`,
  which reads no pre. Its docstring and those of `MachineLive` (`Assembly.lean:244`) and
  `M6Ledger.step_deliver` (`:1416`) say so. The obstacle and the measured repair are under "What is
  owed".
- The admission census is unchanged (final log: "1349 programs reach 48 protocol rows, none with a
  consumed `True` post").

### 6. `storeTyped_of_typedState` (`9247d623`)

`Assembly.lean:294`, proved, `[propext, Quot.sound]`: `MachineTyped root rootTy w m → StoreTyped w`.
The coverage from `WorldValid.heap`/`.promises` over `WorldValid.state`, the stored values from the
generated `HeapCell` column (`StoresOk.c1`), the closing exits from each scope entry's
`ScopeStateOk` (`StoresOk.c3`, the un-refused `ScopeExitOk` arm). 22 lines with its signature
(tested, an `awk` count), so proved rather than declared. It reads only `J`'s `TypedState`.

### 7. Seats E and F against the union: no edit

`Laws/Program/Typed/Seq.lean` and seat E's `Test/Program/TypedProgBindRed.lean` rebuilt after the
`fiberPre` hunk (exit 0); `Laws/Program/Typed/ExitConnector.lean` and `Test/Program/ExitConnector.lean`
rebuilt at the merge (exit 0; they sit outside `Residual`'s cone); all four replay at `9247d623` and
build in the final run (tested).

### 8. The final build

Above, under "Commands and results".

## The ledger, before and after

Per scope, as `#typed_state_obligations` prints (open / proved / total). Before: receipt-B (seat B
alone, `a4fc4b48`), receipt-C (seat C alone, `570142a9`), and the merge `3361bc3d` built here. After:
the final log at `9247d623`.

| Scope | receipt-B | receipt-C | merge (tested) | after (tested) |
| --- | --- | --- | --- | --- |
| `M3bWorld` | 0 / 5 / 5 | 1 open (base, not B's) | 0 / 5 / 5 | 0 / 6 / 6 |
| `M3bAdequacy` | 8 / 66 / 74 | absent | 8 / 66 / 74 | 8 / 66 / 74 |
| `M4Stack` | 0 / 4 / 4 | not reported | 0 / 4 / 4 | 0 / 4 / 4 |
| `M5Hooks` | 0 / 1 / 1 | not reported | 0 / 1 / 1 | 0 / 1 / 1 |
| `M3bAssembly` | not reported | 3 / 1 / 4 | 3 / 1 / 4 | 3 / 1 / 4 |
| `M6Ledger` | 20 / 0 / 20 | 20 / 0 / 20 | 20 / 0 / 20 | 20 / 0 / 20 |
| `M6Edits` | absent | 6 / 7 / 13 | 6 / 7 / 13 | 6 / 7 / 13 |
| `M6Stack` | absent | 3 / 0 / 3 | 3 / 0 / 3 | deleted (two goals restated `M3bWorld`'s; one moved there, proved) |
| `M7` | absent | 4 / 0 / 4 | 4 / 0 / 4 | 4 / 0 / 4 |

Open in these scopes: 44 at the merge, 41 after. Whole tree after (tested,
`python3 ledger_sum.py final1.log`, which keeps each scope's last report): 79 report lines, 72
scopes, 43 open, 441 proved, 484 total. Not compared with receipt-C's whole-tree line: its base
(`bb269fde`) lacks seats B, E and F and its counting command is not recorded.

## Plan §5

1. **Repeated proofs that disappeared.** `M6Stack`'s two goals restated seat B's stack and
   saved-frame laws, and `savedMono_of_stackMono` derived the second from the first a second time:
   gone, one owner (`M3bWorld`). `preds_savedOk_mono` has one proof, in `src`, beside its ledger line
   (the battery uses it). `AwaitLoad`'s copy of the old-post refutation is a reference to seat B's
   proof. Nothing was copied: the historical `OldMachineTyped` is one structure with one changed
   clause.
2. **Program-to-execution connections closed.** `storeTyped_of_typedState`: `J` supplies seat B's
   `StoreTyped`, the premise of the store handler rule `storeStep_typed` (consumption is wave 2's
   `loop` arm: owed). `AwaitLoad.code_typed`/`loadsTyped`: M5's route (`machineTyped_load`, seat E's
   `seq_typed`, the row-136 post) closes end to end on one corpus program with a fork and an await,
   a finite instance, not M5. Open per scope: M5 3, M6 20, `M6Edits` 6, M7 4, `M3bAdequacy` 8.
3. **The eventual claim** is unchanged from receipt-C: M7 (a–c and scope-handle validity) over `J`
   covers the frame machine at the empty host table, on answer-free tapes, with observation `obs`;
   the OCaml engine is outside it until row 28; nothing here is verified lowering or host safety.

## What is owed

- **`M6Ledger.step_deliver` stays refuted** (`E4-SCHED-CE-020`'s witness,
  `step_deliver_refuted_by_absent_scope`). Obstacle (proved and tested): `TypedProg.scopeExit`
  (`Residual.lean`, the inductive's last constructor) has no pre, and the `fiber` arm excludes the
  marker, so no `fiberPre` arm reaches it (the generic `Typed` of `Laws/Effects/Protocol.lean` would
  read the arm at `Ψ_F`; nothing in `src` instantiates it there today, tested with `grep`). Repair, measured on a reverted prototype (tested; `git
  diff` empty after undoing it by inverse edits, since a guardrail hook refused `git checkout`):
  ```lean
    | scopeExit {w : World} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
        (live : (w.state.scopes.entryAt sc).isSome = true)
        (payload : ExitOk w ty ex)
        (next : ∀ w', w.leHost w' → ∀ ans, TypedProg root w' ty (k ans)) :
        TypedProg root w ty (.vis (.inr (.scopeExit prev sc ex)) k)
  ```
  with `TypedProg.fiber_inv`'s pattern `| scopeExit _ _ _ =>`, `typedProg_mono`'s arm
  `.scopeExit (ord.1.1.2.2.2.1 _ live) (strongExit_mono _ _ _ _ ord payload) …`, seat E's
  `Seq.close_typed` arm `| scopeExit live payload _ ih => exact .scopeExit live payload …`, and
  seat C's `RawOrderLoad.fiber_inv` pattern. Everything else in the typed state and its batteries
  built unchanged. In `M6Capstone`, `callback_typed` takes the premise and eight theorems of
  `H1HaltAmendment` fall: `worker_saved`, `typed`, `old_typed` (errors), and through them
  `typedState_input`, `config_input`, `step_deliver_false`, `deliver_preserves_this_state`,
  `step_deliver_refuted_by_absent_scope`. The repaired form elaborated without error in the
  prototype (its axioms were not printed there):
  `input_refused (w) : ¬ ConfigTyped (rootProgram : ProgramSource) unitTy w machine commands`,
  through `ReadCode` (the running worker's queued `deliver` reads its code; the frame's run arm
  types the callback at the current world; the constructor demands scope 0; `WorldValid.state`
  gives the machine's store, which holds none). Keeping the eight as history needs a local copy of
  the pre-premise `TypedProg` and of H1's and the split's states over it. Decision proposed below.
- **`E4-TYPED-CE-009`** stays red (`RawOrderLoad.lean`, unchanged, 5 axiom lines): seat A's `Fits`
  order is not merged.
- Unchanged from the seats' receipts: the eighteen command proofs, the six content edits, M5
  (`denoteR_typed`, `evalTerm_fits`, `typedState_load`), M7 a–c and `exitHandles_valid`, seat B's
  eight `M3bAdequacy` goals and the close rows (rows 151, 152), the layer-reference decision
  (receipt-C's proposed row). Owed consumption: `storeTyped_of_typedState` (wave 2's `loop` arm).
- Bounded evidence: `AwaitLoad`'s positive control is one program at fuel 5 and the empty row table;
  the refusal controls are at concrete worlds; the prototype measurement is one run on this tree.
  Nothing is host-only (no OCaml, no TypeScript was run).

## Lines for the coordinator's files

**`Test/Counterexamples/REGISTER.md`** (receipt-C's proposals, checked against what landed; each
row's other cells stand):

- `E4-TYPED-CE-010`, witness cell, append: "Against M5 and the capstone over `J`:
  `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean`, `loadsTyped`, `capstone_at_load`
  (current: M5's proposition holds at the corpus's `awaitFiber.value`, `code_typed` by `seq_typed`;
  seat I, `cd9a51bf`); `root_code_refused`, `loadsTyped_false`, `capstone_false` (historical, over
  seat B's `OldTypedProg` and `OldMachineTyped`); seat C's script pinned failing (`#guard_msgs`)."
  (receipt-C proposed these two as refutations "before seat B's repair merges"; they are history now.)
- `E4-TYPED-CE-011`: as receipt-C proposes ("REPAIRED 2026-10-01 by row 134's split (seat C):
  `StaleCode.capstone_window_holds`, `machineTyped_m6`, `machineTyped_m9`, `evaluate_entry_m6`;
  the cut refutations retained against `H1Shapes` (`window_untyped`, `capstone_false_window`,
  `ledger_jointly_false_window`)"); checked: `StaleCode` builds unchanged at the union (68 axiom
  lines) and every name exists (tested, `grep`).
- `E4-TYPED-CE-012`, append (replacing receipt-C's "expected to carry (not re-run); `M6Stack`
  declares the two laws"): "At the union (seat I, `4a08dd1b`, `6a477f47`): `step_loop_refuted`
  compiles over `Old.*` (tested); `step_loop_good` is restated over `I` (`good_config`,
  `afterGood_config`); the laws are `M3bWorld`'s (`M6Stack` deleted)."
- `E4-TYPED-CE-013`, append: "The close-scope code control is restated at a live scope (row 139's
  pre, seat I, `509d243c`): `CloseScope.close_code_typed`, `close_code_typed_live`,
  `close_code_refused_absent`."
- `E4-TYPED-CE-014`: as receipt-C proposes ("REPAIRED 2026-10-01 (`J`'s `stuck = none`):
  `machineTyped_not_halted`, `StaleCode.machineTyped_not_halted_here`, `halting_result_outside`;
  H1's facts side by side (`StaleCode.H1.typedState_halt`, `halting_result_typed`,
  `typed_not_imply_running`)"); checked (tested, `grep`).
- `E4-SCHED-CE-019`, append as receipt-C proposes: "under row 134 the terminal witness keeps `I`
  (`M6Capstone.H1TerminalAmendment.deliver_keeps_config`, `result_config_typed`)"; checked: both
  build at the union (`M6Capstone.lean:1705`, `:1690`).
- `E4-SCHED-CE-020`, status "SEEDED (re-opened 2026-10-01)", replacing receipt-C's "until seat B's
  scope-liveness pre on `fiberPre`": "H1's halt tolerance is superseded by row 139; the witness
  refutes the restated `step_deliver` (`M6Capstone.H1HaltAmendment.step_deliver_refuted_by_absent_scope`).
  The `fiberPre` premises landed (seat I, `509d243c`) and do not reach the marker:
  `TypedProg.scopeExit` reads no pre. Open under the proposed row on the scope-exit constructor."

**`docs/core/decisions.md`** (status lines to append; one new row):

- Row 87: "`preds_savedOk_mono` proved in `Laws/Program/Typed/Assembly.lean` and declared in
  `M3bWorld` (seat I, `6a477f47`; `M3bWorld` 0 open, 6 proved, reported once at `Assembly.lean`'s
  foot); `M6Stack` deleted, its two other goals having restated `M3bWorld`'s laws. The other owner
  predicates of `preds` remain to declare."
- Row 134: "Integrated with seat B's closed frames and posts (seat I, `3361bc3d`..receipt): no
  statement of either seat weakened except `ProtocolPosts.close_code_typed` (row 139's hunk makes its
  old form false); `FramesNotKripke.step_loop_good` restated over `I`; the controls the merge flips
  kept as history."
- Row 136: "`E4-TYPED-CE-010` flipped against M5 over `J` (seat I, `cd9a51bf`, `AwaitLoad.loadsTyped`);
  `storeTyped_of_typedState` (`9247d623`) gives `StoreTyped` from `J` for `storeStep_typed`."
- Row 139: "Seat C's `fiberPre` hunk landed by seat I (`509d243c`): declared target for
  `interruptAs`, declared target and live scope for `runIn`, live scope for `forkIn`, `closeScope`,
  `scopeExit`, `raceRegister` refused; refusal controls in `M6Capstone.Liveness` and
  `ProtocolPosts.CloseScope.close_code_refused_absent`. Open: the scope-exit marker (new row);
  `step_deliver` refuted until it lands."
- Row 140: "`M6Stack` folded into `M3bWorld`; `storeTyped_of_typedState` proved (seat I)."
- Row 148: "First positive instance of M5's route over `J` (seat I, `cd9a51bf`): `AwaitLoad.code_typed`
  types the loaded root of `awaitFiber.value` at every world by `seq_typed`, so `loadsTyped` holds
  there (one program, fuel 5); `denoteR_typed` stays declared."
- **New row (proposed): the scope-exit marker's liveness in `TypedProg`.** "`TypedProg` types
  `.scopeExit` through its own constructor, which reads no pre, so row 139's `fiberPre` arm does not
  reach the typed state and `step_deliver` stays refuted (`E4-SCHED-CE-020`). (a) The constructor
  demands the scope's liveness (`live : (w.state.scopes.entryAt sc).isSome = true`, monotone by
  scope persistence); four one-line consumers (`fiber_inv`, `typedProg_mono`, seat E's
  `close_typed`, `RawOrderLoad`); the eight `H1HaltAmendment` controls kept as history over a local
  copy of the judgment without the premise and of H1's and the split's states built on it; the
  repaired form `∀ w, ¬ ConfigTyped … (command :: rest)` replaces the red control (measured,
  receipt-I). (b) As (a), deleting the eight historical controls (their statements recorded at
  `9247d623`). (c) Leave the constructor; carry the liveness of every saved scope-exit frame as a
  `J` clause. Recommendation: (a): it is row 139's rule at the site the typed state reads, it keeps
  every historical control, and the generic protocol judgment already reads the same premise
  through `Ψ_F`." (owner or coordinator)

**`docs/STATE.md`**: "Seat I (2026-10-01): seat C's split integrated with seats B, E and F; `lake
build Effect4.Laws Test.All` green; `M6Stack` folded into `M3bWorld`; `E4-TYPED-CE-010` flipped
(`AwaitLoad.loadsTyped`); `step_deliver` still refuted: the scope-exit constructor (proposed row)."

**`docs/ARCHITECTURE.md`** (not the brief's list; a line for whoever keeps it): "`M3bWorld`'s ledger
report and audit run at the foot of `Laws/Program/Typed/Assembly.lean`, where its last goal
(`preds_savedOk_mono`) is declared." No module was added, moved or removed.

**`docs/core/system-map.md`**: nothing beyond receipt-C's §8 lines.

## Work log (incremental, as written during the work)

- Read in full: `brief-I.md`, `plan.md`, `receipt-B.md`, `receipt-C.md`.
- First narrow build at `3361bc3d`: `LEAN_NUM_THREADS=6 lake build
  Effect4.Laws.Program.Typed.Assembly` (running; seat C's `Typed/Sources.lean` sits under
  `World.lean`, so the typed-state chain recompiles).
- Build at the merge `3361bc3d` (tested): `LEAN_NUM_THREADS=6 lake build
  Effect4.Laws.Program.Typed.Assembly` exit 0, 382 jobs, 8 min 10 s. Ledger printed: `M3bWorld`
  0 open/5 proved/5 total; `M3bAdequacy` 8/66/74; `M4Stack` 0/4/4; `M5Hooks` 0/1/1; `M3bAssembly`
  3/1/4; `M6Ledger` 20/0/20; `M7` 4/0/4; `M6Edits` 6/7/13; `M6Stack` 3/0/3.
- The 20 test modules that import the typed state, one lake call (tested): three fail, each where a
  receipt foresaw it: `M6Capstone.lean:1889` (seat C's `worker_saved`, one-world binders),
  `FramesNotKripke.lean` (the split), `AwaitLoad.lean:98` (seat B's await post). `ProtocolPosts`,
  `StaleCode`, `RawOrderLoad`, `TypedSplit`, `ValueMembership`, `H2PartOne`, `TypedStack` and the
  rest build unchanged.
- Repair 1 (`60bc5d69`): `worker_saved` takes the closed binders. `lake build
  Test.Counterexamples.Machine.Semantics.M6Capstone` exit 0; 123 axiom lines, none with `sorryAx` or
  `Classical.choice`.
- Repair 2 (`4a08dd1b`): `FramesNotKripke` under the split; `step_loop_good` restated over `I`
  (`ConfigTyped`, a strengthening: the old queue-relative `TypedState` typed the root's code, which
  is `ReadCode`'s now), `good_config`/`afterGood_config` new; `preds_savedOk_mono` re-proved by
  `Contracts.stackAccepts_mono`. `lake build Test.Program.FramesNotKripke` exit 0; 19 axiom lines,
  all `[propext, Quot.sound]`.
- Repair 3 (`cd9a51bf`): `AwaitLoad` flipped; history over seat B's `OldTypedProg`; positive
  `loadsTyped`, `capstone_at_load`; fixture pins seat C's script failing. `lake build
  Effect4.Laws.Program.Typed.Assembly Test.Counterexamples.Machine.Semantics.AwaitLoad` exit 0;
  14 axiom lines at `[propext, Quot.sound]`.
- Repair 4 (`6a477f47`): `M6Stack` deleted in favour of `M3bWorld` (row 87's own text puts every
  owner predicate's monotonicity there; `M6Stack`'s two other goals restated B's `M3bWorld` laws,
  so keeping both would duplicate them); `preds_savedOk_mono` proved in `Assembly.lean` beside its
  `M3bWorld` goal; the `M3bWorld` audit and report moved to `Assembly.lean`'s foot. Narrow build of
  `Assembly`, `Seq` and the 14 direct importers of `Residual` and `Assembly`: exit 0, 402 jobs;
  `M3bWorld: 0 open, 6 proved, 6 total; ceiling 0`; audit `5 paired, 1 without a namesake, 0
  mismatches`; `Effect4.Program.Typed.preds_savedOk_mono` and its `.checked` at `[propext, Quot.sound]`.
- Repair 5 (`509d243c`): seat C's hunk on `fiberPre` applied as written; `fiberPre_mono`'s arms
  re-proved; `ProtocolPosts.close_code_typed` restated at a live scope (`close_code_refused_absent`,
  `close_code_typed_live` beside it); four refusal controls in `M6Capstone.Liveness`. Tested: with
  the hunk, `M6Capstone` still builds and `step_deliver_refuted_by_absent_scope` still holds at
  `[propext, Quot.sound]`: `TypedProg.scopeExit` reads no pre. Left red; obstacle in "What is owed".
  Builds: `lake build Effect4.Laws.Program.Typed.Residual` exit 0; the 24-target consumer build
  failed only at `ProtocolPosts.lean:455` (the restated theorem); after it, `lake build
  Test.Program.ProtocolPosts Test.Counterexamples.Machine.Semantics.AwaitLoad` exit 0 and `lake
  build Test.Counterexamples.Machine.Semantics.M6Capstone` exit 0 (127 axiom lines, none with
  `sorryAx` or `Classical.choice`); admission census unchanged ("1349 programs reach 48 protocol
  rows, none with a consumed `True` post").
- Repair 6 (`9247d623`): `storeTyped_of_typedState` proved in `Assembly.lean` (a few lines, so not
  declared). `lake build Effect4.Laws.Program.Typed.Assembly Test.Program.TypedSplit` exit 0; axioms
  `[propext, Quot.sound]`; the 11 direct importers of `Assembly` exit 0.
- Repair 7: no edit. `Seq` and `TypedProgBindRed` rebuilt after the `fiberPre` hunk (exit 0);
  `ExitConnector` and its battery rebuilt at the merge (exit 0; outside `Residual`'s cone); at
  `9247d623` all four replay.
- Measurement for repair 5's follow-up (tested on an uncommitted prototype, then undone by inverse
  edits; `git diff` empty after): the liveness premise on `TypedProg.scopeExit` costs one line in
  `Residual.lean` (`fiber_inv` pattern), one in `typedProg_mono` (scope persistence), one in seat E's
  `Seq.close_typed`, one in seat C's `RawOrderLoad.fiber_inv`; every other module of the typed
  state and its batteries builds unchanged. In `M6Capstone`, `callback_typed` takes the premise and
  eight theorems of `H1HaltAmendment` fall: `worker_saved`, `typed`, `old_typed` (errors) and
  `typedState_input`, `config_input`, `step_deliver_false`, `deliver_preserves_this_state`,
  `step_deliver_refuted_by_absent_scope` (through them). The repaired form `input_refused (w) : ¬
  ConfigTyped rootProgram unitTy w machine commands` elaborated in the prototype (through
  `ReadCode`).
