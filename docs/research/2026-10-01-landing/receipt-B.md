# Seat B receipt: frames closed under world growth, posts the handlers fulfil, the walk

Seat B of the 2026-10-01 landing. Base `bb269fde` on `refactor/phase1-phase3`; branch `seat/B` in
`/Users/pooks/Dev/lean4-effect4-seat-B`; head and commits below. Evidence words: **proved** (a
kernel theorem built here, axioms printed at `[propext, Quot.sound]` or less), **tested** (a
finite check run here), **reading** (code read, not run), **assumed**.

## The one thing first

Saved frames are now closed under world growth (row 135) and every protocol post sits at the
machine's answer (row 136); the handler-adequacy rule is **proved** (`storeStep_typed`, with
`answerFrame_typed` and `seqFrame_typed` for the fiber rows), with 23 of 31 store rows and 40
fiber instances proved and 8 store rows declared. **But the exact close-scope and close-walk post
that row 136's synthesis correction fixed, `ExitOk w' (EffTy.pure .unit) ans`, is not fulfilled by
the handler in two cases, both proved red here, so those two rows need an owner decision before
wave 2 consumes them**: a scope whose lone finalizer answers outside `⟨unit, never⟩`
(`lone_release_outside_post`: a failing `release` finalizer, which the current `scopeAdd` pre
admits; by reading also a lone `acquireRelease` release that answers a non-`unit` value, which the
checker allows, `Effect<unknown, never, R2>`, `Program/Checker.lean:201-209`), and the close walk,
whose iterator protocol cannot carry shape-defect exclusion through reified exits
(`closeSeq_protocol_refused`). Before merging, also know: the branch merges with
`refactor/phase1-phase3` at `e7f9756f` with no textual conflict (`git merge-tree`, tested), and
seat E's `Typed/Seq.lean` uses only `TypedProg`'s constructors, byte-identical here (reading; not
built merged); `M6Capstone.lean` (seat C's) carries a three-lambda hunk from this branch; the new
batteries build typed states through the generated skeleton and `TypedState`, which seat C
restates.

## Base, head and commits

Base `bb269fde` (`refactor/phase1-phase3`). Commits on `seat/B`, in order:

| Commit | Step |
| --- | --- |
| `eb3ab9a9` | 1: the counterexamples on this tree, committed red |
| `074f03ff` | 2: row 135, frames and hook protocols closed under later worlds |
| `894e7512` | 3: row 136, the posts at the machine's answers; the handler-adequacy rule |
| `69063460` | 4: TY-16 and `guard_inv` (`guard_frame`); row 137 reviewed |
| `1e75eb16` | 5: the flips |
| `a4fc4b48` | 5, follow-up: the historical typed state's own inert-code predicate; `preds_savedOk_mono` |
| head | this receipt (the commit that adds this file) |

No push. `git diff --stat bb269fde..a4fc4b48`: 13 files changed, 4266 insertions, 131 deletions.

## Changed paths

Seat B's files:
- `src/Effect4/Laws/Program/Typed/Contracts.lean`: closed frame judgment, imports `Validity`;
  world-growth laws; the frame category laws; `Example` moved out.
- `src/Effect4/Laws/Program/Typed/Residual.lean`: closed hook protocols and their monotonicity;
  `typedProg_mono` and the six helpers; `savedOk_mono`; the posts and pres of row 136;
  `TypedProg.fiber_inv`, `TypedProg.guard_frame`, `guard_inv`'s docstring; `M3bWorld` 0 open.
- `src/Effect4/Laws/Program/Typed/Stack.lean`: `HookLaws` with closed resume tails; the walk,
  `hookLaws_interpR`, `saveAnswerR_typed` restated; imports `Typed/Adequacy.lean`.
- `src/Effect4/Laws/Program/Typed/Adequacy.lean` (new): `StoreTyped`, `StoreImplements`, the
  handler rules, 23 store and 40 fiber instances, the ledger `M3bAdequacy`.
- `Test/Program/FramesNotKripke.lean` (new), `Test/Program/ProtocolPosts.lean` (new).
- `Test/Program/TypedStack.lean`, `Test/Program/TypedControl.lean` (batteries of Stack and Residual).
- `Test/Counterexamples/Machine/Semantics/TrivialPosts.lean`, `Test/Program/AdmissionCensus.lean`
  (batteries of Residual's posts).
- `Test/All.lean`: two imports after `Test.Program.TypedStack` (the anchor the brief names).

Repairs in other seats' files, minimal, listed below as hunks: `Test/Program/H2PartOne.lean`
(`loop_admitted`), `Test/Counterexamples/Machine/Semantics/M6Capstone.lean` (seat C's: three
lambdas). No edit in `Assembly.lean`, `Scheduler.lean` or any seat A file: they build unchanged.

## Commands and results

- Step 1: `LEAN_NUM_THREADS=4 lake build Test.Program.FramesNotKripke Test.Program.ProtocolPosts`:
  "Build completed successfully (379 jobs)".
- Steps 2, 3 and 4, narrow: `LEAN_NUM_THREADS=4 lake build` of
  `Effect4.Laws.Program.Typed.{Contracts,Residual,Stack,Frames,Scheduler,Assembly}` (step 2;
  steps 3 and 4 name `{Residual,Adequacy,Stack,Scheduler,Assembly}`) and the 16 test modules that
  import them (`Test.Audit.TypedStateDecl`, `Test.Counterexamples.Machine.Semantics.{AsyncHookContract,
  InterruptCarrier,InterruptDelivery,M6Capstone,StrongExitDefect,TrivialPosts,ValueMembership}`,
  `Test.Program.{AdmissionCensus,FramesNotKripke,H2PartOne,LoadedAdmission,ProtocolPosts,
  TypedControl,TypedResidual,TypedStack}`): "Build completed successfully (402 jobs)" each time.
  Step 5: `lake build Test.Program.FramesNotKripke Test.Program.ProtocolPosts`, no error; the
  follow-up `a4fc4b48`: `lake build Test.Program.FramesNotKripke`, no error. The two new
  batteries also by `LEAN_NUM_THREADS=4 lake env lean -DwarningAsError=true <file>`, exit 0.
- Final: `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`. First run on `1e75eb16`: "Build
  completed successfully (710 jobs)", exit 0, 7:22 wall; the library-root gate ("134 API/utility
  modules, 213 Laws-only modules; every library source is reachable; Effect4 never reaches Laws")
  and the module and axiom gate ("checked 493 modules and 69957 declarations; semantic/test
  axioms are [propext, Quot.sound]; exact implementation boundary (15 module(s), 23
  declaration(s)) additionally allows Classical.choice"). Rerun on `a4fc4b48`: "Build completed
  successfully (710 jobs)", exit 0, 57.8 s wall (only `Test.All` rebuilt; every other module up to
  date from the narrow builds), the same two gate lines, the second now "checked 493 modules and
  69962 declarations".
- Axioms: `#print axioms` for every theorem in the four source modules other than the ledger
  stubs (`ProofGraph.Obligation … := ⟨⟩`), a scratch file over 131 names run by `lake env lean`
  at `a4fc4b48`: 122 at `[propext, Quot.sound]`, 9 at `[propext]`, none above. Batteries, printed
  by the build: FramesNotKripke 17 lines, all `[propext, Quot.sound]`; ProtocolPosts 44 lines, 39
  `[propext, Quot.sound]` and 5 `[propext]`. Every other declaration of the batteries is held by
  the module and axiom gate of the final build.
- Ledgers printed by the builds: `M3bWorld: 0 open, 5 proved, 5 total; ceiling 0` (at base: 1
  open, 2 proved, 3 total; ceiling 1); `M3bAdequacy: 8 open, 66 proved, 74 total; ceiling 8`
  (new); `M4Stack: 0 open, 4 proved, 4 total; ceiling 0`; `M5Hooks: 0 open, 1 proved, 1 total;
  ceiling 0`; `M6Ledger: 20 open, 0 proved, 20 total; ceiling 20` (unchanged). Audits: `M3bWorld` 4 paired, 1 without a namesake, 0 mismatches; `M3bAdequacy` 65
  paired, 9 without a namesake (the 8 open goals and `guard_frame`, whose law is in Residual), 0
  mismatches.
- Census before rewriting (`scratch/CensusBefore.lean` by `lake env lean`: `#auto_census … using
  aesop` over Contracts, Residual and Stack, and again with `(rule_sets := [Effect4.TypedState])`
  over Residual and Stack): Contracts 0 of 4, Residual 0 of 22 and Stack 1 of 24 (`walk_done`, 3
  lines) closed from their statements under both (tested), so no proof was rewritten against a
  bank.
- `make check-cases`: not run. Its audit imports the core library only (`Makefile:314`, prerequisite
  `.lake/build/lib/lean/Effect4.trace`; `tools/Conform/Effect4/cases.json`, `"imports": ["Effect4"]`),
  which this branch does not touch, and no match added here is on a policy family
  (`cases-policy.json`: `Ty`, `Eff`, `NativeOp`, `RowKind`, `RowShape`, `Registration`, `Lit`,
  `Term`, `CauseTerm`; the added case splits are on the store and fiber operations, exits,
  completions, keys and `Option` equations; reading). No `Ty` case analysis (row 132). No
  generator run.

## Step 1: the counterexamples on this tree (`eb3ab9a9`)

`FramesNotKripke.lean` and `ProtocolPosts.lean`, from the coordinator's ports at `dceae006`
(`docs/research/2026-10-01-landing/ports-at-dceae006/`), plus the two controls the ports lacked,
ported from `docs/research/2026-10-01-formal-pass/algebra/verify-StepLoop.lean` (the port
`HeadStepLoop.lean` lacks them) to the merged typed state: `evaluate_keeps` (the idle
machine started by `evaluate` is the running member of the same family with one more trace event,
`afterEval_machine`, proved by `rfl`) and `step_loop_good` (one `loop` leaves
`[drainDue, deliver root false]`, `afterGood_queue` by `rfl`, and the state is typed at `w1g`, the
world that declares cell 0). Also the program-level await refutation `typedState_load_false`
(`HeadAwaitLoad.lean`). Committed red: each theorem refuted a statement as it stood.

## Step 2: row 135, the Kripke closure (`074f03ff`)

Statements, old and new (statements only; no runtime change):

- `Contracts.FrameAccepts`. Old: `resume.run : ∀ ex, Exits w tin ex → kind.hasExitArm ex = true →
  TypedProg w tout (next ex)`, `resume.skip : ∀ ex, Exits w tin ex → … → Exits w tout ex`,
  `answer.run : ∀ ex, Exits w tin ex → TypedProg w tout (next ex)`, and the hook premises
  `hooks.asyncFinalizer w tin tout name`, `hooks.iterator w …`, `hooks.loop w … cursor`. New: each
  is `∀ w', w.leHost w' → …` with the judgments read at `w'`. The module imports
  `Typed/Validity.lean` (for `World.leHost`) instead of `Typed/World.lean`.
- `IteratorProtocol`, `LoopProtocol`. Old: the world a parameter, `step.next : ∀ v, Fits w v
  tin.answer → IteratorAnswer root w tout …`. New: the world an index (a step's answer lives at a
  later world), `step.next : ∀ w', w.leHost w' → ∀ v, Fits w' v tin.answer → IteratorAnswer root
  w' tout …`, the `resume`/`continue` tail a protocol at the answer's world.
- `frameProtocols.asyncFinalizer`. Old: `tin = tout ∧ ∀ cause, ExitOk w tin (.failure cause) →
  cause.hasInterrupts = true → TypedProg root w tout (…)`. New: `tin = tout ∧ ∀ w', w.leHost w' →
  ∀ cause, ExitOk w' tin (.failure cause) → … → TypedProg root w' tout (…)`.
- `HookLaws`. Old: a resumed protocol `hooks.iterator w tin' tout name'` (loop: `hooks.loop w tin'
  tout name cursor'`). New: `∀ w', w.leHost w' → hooks.iterator w' tin' tout name'` (loop likewise):
  one intermediate type at every later world.
- `saveAnswerR_typed` (and `M4Stack.saveAnswerR_typed`). Old adapter premise `∀ ex, ExitOk w tin ex
  → TypedProg root w middle (next ex)`; new `∀ w', w.leHost w' → ∀ ex, ExitOk w' tin ex →
  TypedProg root w' middle (next ex)`.
- Same text, now over closed stacks: `popR_typed`, `popR_typed_interpR`, `deliver_active`,
  `deliver_stale`, `WalkTyped`, `SavedOk`, `StackAccepts`. The walk reads each frame clause at the
  current world (`run w (leHost_refl w)`); `hookLaws_interpR` re-proved from the closed protocols
  (`iteratorProtocol_mono`, `loopProtocol_mono`): the verifier's "reading, not probed" is now proved.
- `M3bWorld`: `typedProg_mono` proved (it was the open goal); `stackAccepts_mono` and
  `savedOk_mono` declared and proved; ceiling 1 → 0. `Contracts.Example` moved to
  `Test/Program/TypedStack.lean` (the plan's T3, "controls to `Test/`", listed under seat C; done
  here for this seat's own module). `Typed/Frames.lean` needed no change.

## Step 3: row 136, the posts and the handler rule (`894e7512`)

| Row | Old | New |
| --- | --- | --- |
| `fiberPost (.await t .awaitValue)` | `∃ ty, w'.Γ t = some ty ∧ Fits w' ans ty.answer` | `∃ ty, w'.Γ t = some ty ∧ Fits w' ans (.exitOf ty.answer ty.error)` |
| `fiberPost (.closeScope _ ex)`, `(.closeIter _ _ ex)` | `ans = ex` | `ExitOk w' (EffTy.pure .unit) ans` |
| `storePost (.scopeRemove _ _)` | `∃ b, ans = Val.bool b` | `ans = Val.unit` |
| `storePost (.deferredAwaitCleanup _ _ _)` | `∃ b, ans = Val.bool b` | `ans = Val.unit` |
| `storePost (.scopeAdd _ _)` | `∃ b, ans = Val.bool b` | `ans = Val.unit ∨ ∃ ex, ans = reifyExitVal ex ∧ FitsExit w' ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex` |
| `storePost (.memoRelease _ _)` | `ans = Val.unit` | `ans = Val.unit ∨ ∃ sc, ans = Val.scopeHandle sc` |
| `storePre (.refModify cell _)`, `(.refModifySome cell _)` | `∃ ty, w.Ρ cell = some ty` | `RefDeclared w cell .nat` (the native row's declared cell type) |
| `storePre` of `scopeAdd`, `scopeRemove`, `scopeIsClosed`, `scopeFork` | `True` | `(w.state.scopes.entryAt scope).isSome = true` |
| `storePre (.deferredCompleteWith key c)` | `(w.«Π» key).isSome = true` | `∃ a e, w.«Π» key = some (a, e) ∧` (`.ofExit ex` ⇒ `ExitOk w ⟨a, e, ∅⟩ ex`; `.ofRefGet cell` ⇒ `∃ t, w.Ρ cell = some t ∧ t.sub a = true`) |

The last row is beyond the brief's list: the old pre admitted a completion no later world types
(proved red, `completeWith_old_adequacy_false`: an ill-typed completion of a declared promise
leaves no world over the new store above the old one, since the world order keeps every declared
promise's stored completion typed).

The handler rule, in `Typed/Adequacy.lean` (beside the protocol tables, as the brief allows; the
generic `Protocol.Typed` in `Laws/Effects/Protocol.lean` is seat E's and untouched):
`StoreTyped w`; `StoreImplements root op := ∀ w cert, StoreTyped w → storePre root w op cert →
∃ st' ans, syncOpStep op w.state = some (st', ans) ∧ ∃ w', w.leHost w' ∧ w'.state = st' ∧
StoreTyped w' ∧ storePost w' op cert ans`; `storeStep_typed` (from `StoreImplements root op`, a
typed `vis (.inl op) k` and `StoreTyped w`: the store steps to `(st', ans)` and `k ans` is typed at
a later world over `st'`, typed again); `storeStep_answers` (the evaluator's frontier branch,
`EvaluateR.lean:304`, which answers `unit` whatever the post says, is never taken by typed code
over a typed store at a fulfilled row);
`answerFrame_typed`, `seqFrame_typed` (the frame the evaluator saves accepts every exit the row's
post admits, the fiber analogue through the `FiberAction` helpers). The statement covers the
frontier arm by its first conjunct, which the verifier found missing from an adequacy over `some`
results alone (`proofs/verify.md` G6c (3)).

## Step 4: TY-16, `guard_inv`, row 137 (`69063460`)

`TypedProg.fiber_inv` (TY-16) landed with step 3 beside `guard_inv` (the fiber instances use it).
`guard_inv`'s docstring said "exactly" `FrameAccepts.resume`; before row 135 the frame arms were
one-world, so that was false. It is now the theorem `TypedProg.guard_frame` (the body at `mid`, and
the frame `saveR` pushes, `.resume kind (fun ex => k (some ex))`, accepted from `mid` to the
guard's type at every later world), the guard row's `M3bAdequacy` instance; the docstring says so.
Row 137, per amendment 3 and the owner's ratification: `asyncPre`'s arms (the timer's `unit`, the
deferred's declared columns, the host row's declared columns) and `fiberPre`'s `awaitAll`/`raceAll`
compare a type with a certificate the typing derivation chooses; kept in `Ty.sub`
(`fits_normalize` bridges a certificate to the checker's normalized type), verdict in
`asyncPre`'s docstring. No other Residual entry compares a declared type with a certificate
(reading: the entries with `.sub` are `Residual.lean:56`, `:135`, `:137`, `:139-140`, `:153`,
`:155`; `:56` is the new completion arm, seat A item 6).

## Step 5: the flips (`1e75eb16`, `a4fc4b48`, and the flips steps 2 and 3 needed)

Every `*_post_excludes` whose post changed has its `*_post_admits` on the real answer
(`scopeRemove`, `scopeAdd`, `awaitCleanup`, `memoRelease`, close-scope, close-walk, await by value),
kept beside the historical exclusion. Where the post stayed and the pre was the defect,
`refModifySome_post_excludes` and `scopeIsClosed_post_excludes_unit` stay green as facts about the
current post, and `refModify_pre_refuses`, `refModifySome_pre_refuses`, `scopeIsClosed_pre_refuses`
and `completeWith_pre_refuses` show the new pre refusing the request the old one admitted, with
`refModify_post_admits` and `scopeIsClosed_post_admits` on the answers the admitted requests get.
The checked code the old posts refused is typed (`close_code_typed`, `await_code_typed`).
`step_loop_good` stays green over the current typed state; `stackAccepts_not_mono` is retained
over `Old.StackAccepts`, and `stackAccepts_mono` is proved on the closed judgment
(`good_stack_transports` uses it). `typedState_load_false` stays a historical control over
`AwaitLoad.OldLoaded`. The historical copies carry their own
`TerminalFiber`/`TerminalPosition`/`CodeInert` (as of `bb269fde`), so they do not follow seat C's
restatement.

## Theorems landed in the source modules

New, restated or re-proved; unchanged theorems of the same modules are not listed. Every row was
printed by `#print axioms` (see Commands).

| Theorem | File:line | Axioms | Status |
| --- | --- | --- | --- |
| `Contracts.frameAccepts_mono` | `Typed/Contracts.lean:113` | `[propext, Quot.sound]` | new |
| `Contracts.stackAccepts_mono` | `Typed/Contracts.lean:131` | `[propext, Quot.sound]` | new |
| `Contracts.savedOk_mono` | `Typed/Contracts.lean:139` | `[propext, Quot.sound]` | new |
| `Contracts.stackAccepts_append` | `Typed/Contracts.lean:154` | `[propext, Quot.sound]` | new |
| `Contracts.stackAccepts_split` | `Typed/Contracts.lean:162` | `[propext, Quot.sound]` | new |
| `Contracts.stackAccepts_id` | `Typed/Contracts.lean:174` | `[propext, Quot.sound]` | new |
| `Contracts.stackAccepts_push` | `Typed/Contracts.lean:177` | `[propext, Quot.sound]` | new |
| `TypedProg.fiber_inv` | `Typed/Residual.lean:269` | `[propext, Quot.sound]` | new |
| `TypedProg.guard_inv` | `Typed/Residual.lean:290` | `[propext, Quot.sound]` | docstring corrected (statement unchanged) |
| `iteratorProtocol_mono` | `Typed/Residual.lean:381` | `[propext, Quot.sound]` | new |
| `loopProtocol_mono` | `Typed/Residual.lean:389` | `[propext, Quot.sound]` | new |
| `asyncFinalizerProtocol_mono` | `Typed/Residual.lean:397` | `[propext, Quot.sound]` | new |
| `TypedProg.guard_frame` | `Typed/Residual.lean:407` | `[propext, Quot.sound]` | new |
| `envTyped_mono` | `Typed/Residual.lean:527` | `[propext, Quot.sound]` | new |
| `pointTyped_mono` | `Typed/Residual.lean:531` | `[propext, Quot.sound]` | new |
| `bodyTyped_mono` | `Typed/Residual.lean:536` | `[propext, Quot.sound]` | new |
| `storePre_mono` | `Typed/Residual.lean:547` | `[propext, Quot.sound]` | new |
| `asyncPre_mono` | `Typed/Residual.lean:588` | `[propext, Quot.sound]` | new |
| `fiberPre_mono` | `Typed/Residual.lean:603` | `[propext, Quot.sound]` | new |
| `typedProg_mono` | `Typed/Residual.lean:647` | `[propext, Quot.sound]` | new (closes `M3bWorld.typedProg_mono`) |
| `savedOk_mono` | `Typed/Residual.lean:668` | `[propext, Quot.sound]` | new |
| `popR_typed` | `Typed/Stack.lean:142` | `[propext, Quot.sound]` | re-proved over closed frames (statement text unchanged) |
| `hookLaws_interpR` | `Typed/Stack.lean:343` | `[propext, Quot.sound]` | re-proved for the closed protocols (`HookLaws` restated) |
| `popR_typed_interpR` | `Typed/Stack.lean:373` | `[propext, Quot.sound]` | statement text unchanged; closed frames |
| `saveAnswerR_typed` | `Typed/Stack.lean:385` | `[propext, Quot.sound]` | restated: adapter premise at every later world |
| `deliver_active` | `Typed/Stack.lean:404` | `[propext, Quot.sound]` | statement and proof text unchanged; stacks now closed |
| `deliver_stale` | `Typed/Stack.lean:419` | `[propext, Quot.sound]` | unchanged (no typing) |
| `storeStep_typed` | `Typed/Adequacy.lean:56` | `[propext, Quot.sound]` | new |
| `storeStep_answers` | `Typed/Adequacy.lean:67` | `[propext, Quot.sound]` | new |
| `restate_world` | `Typed/Adequacy.lean:79` | `[propext, Quot.sound]` | new |
| `same_world` | `Typed/Adequacy.lean:125` | `[propext, Quot.sound]` | new |
| `fits_nat_val` | `Typed/Adequacy.lean:135` | `[propext, Quot.sound]` | new |
| `fits_unit_val` | `Typed/Adequacy.lean:142` | `[propext, Quot.sound]` | new |
| `modify_nat` | `Typed/Adequacy.lean:149` | `[propext]` | new |
| `modifySome_nat` | `Typed/Adequacy.lean:153` | `[propext]` | new |
| `cell_readable` | `Typed/Adequacy.lean:158` | `[propext, Quot.sound]` | new |
| `promise_readable` | `Typed/Adequacy.lean:163` | `[propext, Quot.sound]` | new |
| `nat_cell` | `Typed/Adequacy.lean:169` | `[propext, Quot.sound]` | new |
| `insert_coverage` | `Typed/Adequacy.lean:181` | `[propext]` | new |
| `cancel_completions` | `Typed/Adequacy.lean:194` | `[propext]` | new |
| `complete_cellAt` | `Typed/Adequacy.lean:216` | `[propext]` | new |
| `complete_cells_length` | `Typed/Adequacy.lean:236` | `[propext]` | new |
| `completionOk_of_fitsExit` | `Typed/Adequacy.lean:247` | `[propext, Quot.sound]` | new |
| `poke_world` | `Typed/Adequacy.lean:261` | `[propext, Quot.sound]` | new |
| `complete_world` | `Typed/Adequacy.lean:338` | `[propext, Quot.sound]` | new |
| `scopeRemove_implements` | `Typed/Adequacy.lean:405` | `[propext, Quot.sound]` | new |
| `scopeAdd_implements` | `Typed/Adequacy.lean:412` | `[propext, Quot.sound]` | new |
| `deferredAwaitCleanup_implements` | `Typed/Adequacy.lean:436` | `[propext, Quot.sound]` | new |
| `memoRelease_implements` | `Typed/Adequacy.lean:443` | `[propext, Quot.sound]` | new |
| `refModify_implements` | `Typed/Adequacy.lean:459` | `[propext, Quot.sound]` | new |
| `refModifySome_implements` | `Typed/Adequacy.lean:473` | `[propext, Quot.sound]` | new |
| `refMake_implements` | `Typed/Adequacy.lean:488` | `[propext, Quot.sound]` | new |
| `refGet_implements` | `Typed/Adequacy.lean:537` | `[propext, Quot.sound]` | new |
| `refSet_implements` | `Typed/Adequacy.lean:547` | `[propext, Quot.sound]` | new |
| `refGetAndSet_implements` | `Typed/Adequacy.lean:558` | `[propext, Quot.sound]` | new |
| `refSetAndGet_implements` | `Typed/Adequacy.lean:570` | `[propext, Quot.sound]` | new |
| `deferredMake_implements` | `Typed/Adequacy.lean:581` | `[propext, Quot.sound]` | new |
| `deferredIsDone_implements` | `Typed/Adequacy.lean:609` | `[propext, Quot.sound]` | new |
| `deferredPoll_implements` | `Typed/Adequacy.lean:618` | `[propext, Quot.sound]` | new |
| `deferredCompleteWith_implements` | `Typed/Adequacy.lean:627` | `[propext, Quot.sound]` | new |
| `deferredInterruptWith_implements` | `Typed/Adequacy.lean:643` | `[propext, Quot.sound]` | new |
| `clockNow_implements` | `Typed/Adequacy.lean:651` | `[propext, Quot.sound]` | new |
| `sleepCancel_implements` | `Typed/Adequacy.lean:655` | `[propext, Quot.sound]` | new |
| `scopeMake_implements` | `Typed/Adequacy.lean:662` | `[propext, Quot.sound]` | new |
| `scopeIsClosed_implements` | `Typed/Adequacy.lean:669` | `[propext, Quot.sound]` | new |
| `scopeFork_implements` | `Typed/Adequacy.lean:684` | `[propext, Quot.sound]` | new |
| `memoFork_implements` | `Typed/Adequacy.lean:700` | `[propext, Quot.sound]` | new |
| `memoBuild_implements` | `Typed/Adequacy.lean:707` | `[propext, Quot.sound]` | new |
| `answerFrame_typed` | `Typed/Adequacy.lean:746` | `[propext, Quot.sound]` | new |
| `seqFrame_typed` | `Typed/Adequacy.lean:753` | `[propext, Quot.sound]` | new |
| `closeScope_frame` | `Typed/Adequacy.lean:767` | `[propext, Quot.sound]` | new |
| `closeIter_frame` | `Typed/Adequacy.lean:776` | `[propext, Quot.sound]` | new |
| `awaitValue_frame` | `Typed/Adequacy.lean:785` | `[propext, Quot.sound]` | new |
| `awaitValue_delivered` | `Typed/Adequacy.lean:794` | `[propext, Quot.sound]` | new |
| `joinEffect_frame` | `Typed/Adequacy.lean:800` | `[propext, Quot.sound]` | new |
| `joinEffect_delivered` | `Typed/Adequacy.lean:808` | `[propext, Quot.sound]` | new |
| `mask_frame` | `Typed/Adequacy.lean:816` | `[propext, Quot.sound]` | new |
| `scoped_frame` | `Typed/Adequacy.lean:824` | `[propext, Quot.sound]` | new |
| `gen_frame` | `Typed/Adequacy.lean:832` | `[propext, Quot.sound]` | new |
| `loop_frame` | `Typed/Adequacy.lean:840` | `[propext, Quot.sound]` | new |
| `raceAll_frame` | `Typed/Adequacy.lean:848` | `[propext, Quot.sound]` | new |
| `raceRegister_frame` | `Typed/Adequacy.lean:856` | `[propext, Quot.sound]` | new |
| `async_frame` | `Typed/Adequacy.lean:864` | `[propext, Quot.sound]` | new |
| `yieldNow_frame` | `Typed/Adequacy.lean:875` | `[propext, Quot.sound]` | new |
| `interrupt_frame` | `Typed/Adequacy.lean:883` | `[propext, Quot.sound]` | new |
| `interruptAs_frame` | `Typed/Adequacy.lean:891` | `[propext, Quot.sound]` | new |
| `interruptScoped_frame` | `Typed/Adequacy.lean:899` | `[propext, Quot.sound]` | new |
| `interruptAll_frame` | `Typed/Adequacy.lean:907` | `[propext, Quot.sound]` | new |
| `cancelRace_frame` | `Typed/Adequacy.lean:915` | `[propext, Quot.sound]` | new |
| `awaitNewChildren_frame` | `Typed/Adequacy.lean:923` | `[propext, Quot.sound]` | new |
| `awaitAll_frame` | `Typed/Adequacy.lean:933` | `[propext, Quot.sound]` | new |
| `awaitAllFailFast_frame` | `Typed/Adequacy.lean:941` | `[propext, Quot.sound]` | new |
| `awaitAll_delivered` | `Typed/Adequacy.lean:952` | `[propext, Quot.sound]` | new |
| `awaitAllFailFast_delivered` | `Typed/Adequacy.lean:959` | `[propext, Quot.sound]` | new |
| `getId_answers` | `Typed/Adequacy.lean:968` | `[propext, Quot.sound]` | new |
| `sync_answers` | `Typed/Adequacy.lean:971` | `[propext, Quot.sound]` | new |
| `ambientScope_answers` | `Typed/Adequacy.lean:973` | `[propext, Quot.sound]` | new |
| `setContext_answers` | `Typed/Adequacy.lean:976` | `[propext, Quot.sound]` | new |
| `fork_answers` | `Typed/Adequacy.lean:979` | `[propext, Quot.sound]` | new |
| `forkIn_answers` | `Typed/Adequacy.lean:987` | `[propext, Quot.sound]` | new |
| `forkScoped_answers` | `Typed/Adequacy.lean:996` | `[propext, Quot.sound]` | new |
| `getContext_answers` | `Typed/Adequacy.lean:1006` | `[propext, Quot.sound]` | new |
| `runIn_answers` | `Typed/Adequacy.lean:1011` | `[propext, Quot.sound]` | new |
| `dropObservers_answers` | `Typed/Adequacy.lean:1014` | `[propext, Quot.sound]` | new |
| `closeWalk_answers` | `Typed/Adequacy.lean:1017` | `[propext, Quot.sound]` | new |
| `foreignRelease_answers` | `Typed/Adequacy.lean:1020` | `[propext, Quot.sound]` | new |
| `snapshotChildren_answers` | `Typed/Adequacy.lean:1024` | `[propext, Quot.sound]` | new |
| `closeWalk_typed` | `Typed/Adequacy.lean:1041` | `[propext, Quot.sound]` | new |
| `closeScope_installs` | `Typed/Adequacy.lean:1052` | `[propext, Quot.sound]` | new |

## Controls in the batteries

| Control | File:line | Axioms | Kind |
| --- | --- | --- | --- |
| `stackAccepts_not_mono` | `Test/Program/FramesNotKripke.lean:237` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `typed` | `Test/Program/FramesNotKripke.lean:450` | `[propext, Quot.sound]` | historical: the old typed state holds at the bad machine |
| `queue` | `Test/Program/FramesNotKripke.lean:488` | `[propext, Quot.sound]` | current `QueueOk` at the bad machine |
| `post_untyped` | `Test/Program/FramesNotKripke.lean:532` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `step_loop_refuted` | `Test/Program/FramesNotKripke.lean:559` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `evaluate_keeps` | `Test/Program/FramesNotKripke.lean:598` | `[propext, Quot.sound]` | historical control: `evaluate` keeps the old typed state (the allocation is `loop`'s) |
| `step_loop_good` | `Test/Program/FramesNotKripke.lean:872` | `[propext, Quot.sound]` | current judgment, positive (green) |
| `bad_not_kripke_initial` | `Test/Program/FramesNotKripke.lean:881` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `frameAccepts_now` | `Test/Program/FramesNotKripke.lean:929` | `[propext, Quot.sound]` | conservativity: closed gives one-world at the current world |
| `stackAccepts_now` | `Test/Program/FramesNotKripke.lean:942` | `[propext, Quot.sound]` | conservativity: closed gives one-world at the current world |
| `good_stack_transports` | `Test/Program/FramesNotKripke.lean:951` | `[propext, Quot.sound]` | current judgment, positive |
| `preds_savedOk_mono` | `Test/Program/FramesNotKripke.lean:960` | `[propext, Quot.sound]` | current judgment, positive (for seat C) |
| `bad_not_kripke_by_transport` | `Test/Program/FramesNotKripke.lean:976` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `hookLawsX_old` | `Test/Program/FramesNotKripke.lean:1030` | `[propext, Quot.sound]` | historical: the old hook laws admit the per-world hooks |
| `hookLawsX_refused` | `Test/Program/FramesNotKripke.lean:1056` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `output_typed_one_world` | `Test/Program/FramesNotKripke.lean:1085` | `[propext, Quot.sound]` | historical: the old judgment types the walk's output at one world |
| `output_not_kripke` | `Test/Program/FramesNotKripke.lean:1095` | `[propext, Quot.sound]` | red: wrapping at the frame does not survive the walk |
| `StoreUnit.scopeAdd_open_answer` | `Test/Program/ProtocolPosts.lean:179` | `[propext]` | machine fact (no judgment) |
| `StoreUnit.scopeRemove_post_excludes` | `Test/Program/ProtocolPosts.lean:183` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `StoreUnit.scopeAdd_post_excludes` | `Test/Program/ProtocolPosts.lean:187` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `StoreUnit.awaitCleanup_post_excludes` | `Test/Program/ProtocolPosts.lean:191` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `StoreUnit.scopeRemove_post_admits` | `Test/Program/ProtocolPosts.lean:196` | `[propext, Quot.sound]` | current judgment, positive |
| `StoreUnit.scopeAdd_post_admits` | `Test/Program/ProtocolPosts.lean:200` | `[propext, Quot.sound]` | current judgment, positive |
| `StoreUnit.awaitCleanup_post_admits` | `Test/Program/ProtocolPosts.lean:204` | `[propext, Quot.sound]` | current judgment, positive |
| `StoreUnit.store_step_leaves_typing` | `Test/Program/ProtocolPosts.lean:238` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `StoreUnit.code_refused` | `Test/Program/ProtocolPosts.lean:246` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `Memo.memoRelease_answers_scope` | `Test/Program/ProtocolPosts.lean:267` | `[propext]` | machine fact (no judgment) |
| `Memo.memoRelease_post_excludes` | `Test/Program/ProtocolPosts.lean:271` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `Memo.memoRelease_post_admits` | `Test/Program/ProtocolPosts.lean:276` | `[propext, Quot.sound]` | current judgment, positive |
| `Memo.memo_admitted` | `Test/Program/ProtocolPosts.lean:287` | `[propext, Quot.sound]` | historical: the old judgment admits the program |
| `Memo.memo_next_untyped` | `Test/Program/ProtocolPosts.lean:298` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `Memo.memoCode_refused` | `Test/Program/ProtocolPosts.lean:308` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `Modify.adequacy_false_refModify` | `Test/Program/ProtocolPosts.lean:349` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `Modify.refModifySome_post_excludes` | `Test/Program/ProtocolPosts.lean:356` | `[propext, Quot.sound]` | post unchanged: refuses a bool answer |
| `Modify.refModify_post_admits` | `Test/Program/ProtocolPosts.lean:364` | `[propext, Quot.sound]` | current judgment, positive |
| `Modify.refModify_pre_refuses` | `Test/Program/ProtocolPosts.lean:368` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `Modify.refModifySome_pre_refuses` | `Test/Program/ProtocolPosts.lean:377` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `Frontier.scopeIsClosed_unknown` | `Test/Program/ProtocolPosts.lean:393` | `[propext]` | machine fact (no judgment) |
| `Frontier.scopeIsClosed_post_excludes_unit` | `Test/Program/ProtocolPosts.lean:398` | `[propext, Quot.sound]` | post unchanged: refuses the frontier answer |
| `Frontier.scopeIsClosed_post_admits` | `Test/Program/ProtocolPosts.lean:404` | `[propext, Quot.sound]` | current judgment, positive |
| `Frontier.scopeIsClosed_pre_refuses` | `Test/Program/ProtocolPosts.lean:409` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |
| `CloseScope.close_no_finalizer` | `Test/Program/ProtocolPosts.lean:429` | `[propext]` | machine fact (no judgment) |
| `CloseScope.post_excludes_answer` | `Test/Program/ProtocolPosts.lean:432` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `CloseScope.close_code_refused` | `Test/Program/ProtocolPosts.lean:437` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `CloseScope.post_admits_answer` | `Test/Program/ProtocolPosts.lean:449` | `[propext, Quot.sound]` | current judgment, positive |
| `CloseScope.close_code_typed` | `Test/Program/ProtocolPosts.lean:452` | `[propext, Quot.sound]` | current judgment, positive |
| `CloseScope.lone_release_answer` | `Test/Program/ProtocolPosts.lean:469` | `[propext]` | machine fact (no judgment) |
| `CloseScope.lone_release_outside_post` | `Test/Program/ProtocolPosts.lean:472` | `[propext, Quot.sound]` | red: refutes a current statement (finding) |
| `CloseScope.release_registration_admitted` | `Test/Program/ProtocolPosts.lean:478` | `[propext, Quot.sound]` | current pre admits the failing finalizer (finding) |
| `CloseIter.closeSeq_done` | `Test/Program/ProtocolPosts.lean:498` | `[propext, Quot.sound]` | machine fact (no judgment) |
| `CloseIter.closeIter_post_excludes` | `Test/Program/ProtocolPosts.lean:501` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `CloseIter.closeIter_post_admits` | `Test/Program/ProtocolPosts.lean:506` | `[propext, Quot.sound]` | current judgment, positive |
| `CloseIter.closeSeq_protocol_refused` | `Test/Program/ProtocolPosts.lean:521` | `[propext, Quot.sound]` | red: refutes a current statement (finding) |
| `AwaitValue.post_excludes_delivered` | `Test/Program/ProtocolPosts.lean:568` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `AwaitValue.await_code_refused` | `Test/Program/ProtocolPosts.lean:575` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `AwaitValue.post_admits_delivered` | `Test/Program/ProtocolPosts.lean:584` | `[propext, Quot.sound]` | current judgment, positive |
| `AwaitValue.await_code_typed` | `Test/Program/ProtocolPosts.lean:588` | `[propext, Quot.sound]` | current judgment, positive |
| `AwaitLoad.root_code_refused` | `Test/Program/ProtocolPosts.lean:656` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `AwaitLoad.typedState_load_false` | `Test/Program/ProtocolPosts.lean:731` | `[propext, Quot.sound]` | historical: refutes the old judgment |
| `CompleteWith.completeWith_old_adequacy_false` | `Test/Program/ProtocolPosts.lean:784` | `[propext, Quot.sound]` | historical (finding): the old pre admitted a completion no later world types |
| `CompleteWith.completeWith_pre_refuses` | `Test/Program/ProtocolPosts.lean:798` | `[propext, Quot.sound]` | current judgment refuses what the old admitted |

Ten `#guard_msgs (error)` fixtures in `ProtocolPosts.lean` (the old exclusion proofs for
`scopeRemove`, `scopeAdd`, `deferredAwaitCleanup`, `memoRelease`, close-scope, close-walk and await
by value, and the old pre proofs for `refModify` at a `bool` cell, `scopeIsClosed` on an unknown
scope and `deferredCompleteWith` with an ill-typed completion, each run against the current row
and pinned failing), and one in `FramesNotKripke.lean` (the one-world acceptance script for
`.answer badNext`, verbatim, three pinned errors against the closed judgment).

## The findings for the owner (row 136's close rows)

1. **Close-scope, a lone finalizer** (proved red: `CloseScope.lone_release_answer`,
   `lone_release_outside_post`, `release_registration_admitted`). `Scope.close` with one finalizer
   returns that finalizer's program directly (`closeScopeUnsafeR`, `InterpR.lean:157-164`; rc.112
   `scopeCloseUnsafe`, `internal/effect.ts:3779-3798`, which returns
   `finalizers.values().next().value!(exit_)` at `:3795`). A failing `release` finalizer
   (`FinName.release label true`, `DenoteR.lean:252-253`), which the current `scopeAdd` pre
   (liveness) admits, answers a typed failure outside `⟨unit, never⟩`. By reading, an
   `acquireRelease` release answers its own value (`denoteFin (.foreign c)`, `DenoteR.lean:261`,
   runs the masked `.release` body, whose denotation runs the release under `onExitR`,
   `InterpR.lean:182`), and the checker allows any answer (`Program/Checker.lean:201-209`,
   `Effect<unknown, never, R2>`), so a lone release answering `nat 5` also falls outside the exact
   post. What is proved: `closeScope_installs`, the installed close program typed at
   `⟨unit, never⟩` given the lone finalizer's program is; zero finalizers install `void`, and two
   or more install the walk, typed by `closeWalk_typed` against the `closeWalk`/`closeIter` posts
   (whether the walk's answer lies in that post is finding 2). Line numbers here are at
   `bb269fde`. Options: (a) the scope store's typing types every registered finalizer's program
   at `⟨unit, never⟩`, with `scopeAdd`'s pre demanding it and the foreign finalizer voiding the
   release's value in its denotation (`denoteFin`, not this seat's file; changes the term, not
   rc.112's observable type, which is `void`); (b) the close-scope post admits a success at any live value or a clean
   failure, and the denotation of the user-facing `closeScope` voids the answer before its
   continuation (`DenoteR.lean:197`); (c) leave `closeScope`'s handler side as the stated
   hypothesis. **Recommendation: (a)**: it keeps the checker's `void` and the exact post, and it is
   the typing rc.112's own types already promise (`Effect<void>` finalizers).
2. **The close walk** (proved red: `CloseIter.closeSeq_protocol_refused`). The walk runs each
   finalizer under the `Exit` guard and passes the reified exit on as a value; value membership at
   an exit type (`Fits` at `exitOf`, `Membership.lean`) admits every defect, so a reified `badName`
   failure fits `exitOf unit never`, the walk then halts with it, and `ExitOk` at `⟨unit, never⟩`
   refuses that exit: no iterator protocol types the walk at the exact post. Options: (a) `Fits` at
   `exitOf a e` excludes `badName`/`notImplemented` in the encoded cause (H2 part one's shape
   exclusion carried into reified exits; seat A's module, rows 107/136); (b) the close-walk post
   drops the shape exclusion, which `TypedProg` then refuses for the denoted `vis closeIter pure`
   at any `ExitOk` type; (c) a walk invariant outside the protocol, in wave 2. **Recommendation:
   (a)**, one clause in `Membership.lean`; with it the walk's protocol is provable for clean
   finalizers and `closeSeq_protocol_refused` flips.
3. **`deferredCompleteWith`** (repaired here, proved red and flipped): listed for the register
   under `E4-TYPED-CE-013`.

## For seat A (exact lines)

1. When `Equiv` (`Membership.lean:25`) compares in `subN`: in `Typed/Adequacy.lean`, `nat_cell`'s
   `fits_sub w equiv.1 a fa` → `fits_subN w equiv.1 a fa`; `refModify_implements`'s and
   `refModifySome_implements`'s `fits_sub w equiv.2 _ trivial` → `fits_subN w equiv.2 _ trivial`
   (three tokens, assuming `fits_subN` has `fits_sub`'s shape). `ProtocolPosts.refModify_pre_refuses`
   and `refModifySome_pre_refuses` refute `Ty.bool.sub Ty.nat = true` by `decide +kernel`; with
   `subN` the same call should refute `Ty.bool.subN Ty.nat = true` (assumed, not run).
2. If `World.le` gains a conjunct (`serviceTy` fixed by the order, row 112): the anonymous-
   constructor order proofs gain it: `Typed/Adequacy.lean` `restate_world`, `poke_world`,
   `complete_world` (each `⟨⟨⟨fun _ h => h, le⟩, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
   ⟨?_, ?_⟩, fun _ _ _ h => h⟩, ext⟩`), `FramesNotKripke.lean` `w0_le_w1`, `w0_le_w1g`. Every world
   this seat builds is a record update (`{ initialWorld … with … }`, `{ w with state := … }`), so a
   new field needs nothing else.
3. `Residual.lean` `fiberPre_mono`, the `setContext` arm: `servicesFit_map hPi hRho ord.2 h`
   follows `servicesFit_map`'s premises.
4. Proposed for `Membership.lean` (row 132): move `fits_nat_val` and `fits_unit_val` there from
   `Typed/Adequacy.lean`, and add `theorem fits_nat_irrel (w : World) (n m : Nat) : ∀ t, Fits w
   (Val.nat n) t → Fits w (Val.nat m) t` (one induction over the membership fold); with it and a
   `cases f` lemma on `FnName.total`/`partialUpdate`, the six `f.total` ref rows of `M3bAdequacy`
   close by `poke_world`.
5. Finding 2's option (a): the clause at `exitOf` in `Fits`.
6. Row 137 at `World.lean:81` (`CompletionOk.ofRefGet`, `ty.sub types.1`): this branch's new
   `deferredCompleteWith` pre has the same arm (`Residual.lean:56`, `t.sub a = true`) and
   `deferredCompleteWith_implements` closes it by `exact strong` (`Adequacy.lean:638`), so the two
   must change in one commit: `t.sub a = true` → `t.subN a = true` at `Residual.lean:56`, nothing
   else (reading).

## For seat C (exact lines)

1. The `M6Capstone.lean` hunk this branch carries (keep it when restating; it changes only the
   binders of three lambdas, for the closed `answer` and `resume` arms):

```diff
diff --git a/Test/Counterexamples/Machine/Semantics/M6Capstone.lean b/Test/Counterexamples/Machine/Semantics/M6Capstone.lean
index acc10ff4..d04eb701 100644
--- a/Test/Counterexamples/Machine/Semantics/M6Capstone.lean
+++ b/Test/Counterexamples/Machine/Semantics/M6Capstone.lean
@@ -1235,7 +1235,7 @@ theorem saved_typed : SavedOk (TypedProg (rootProgram : ProgramSource)) ExitOk
     (frameProtocols (rootProgram : ProgramSource)) world unitTy fiber.frame :=
   ⟨natTy, TypedProg.pure (ty := natTy) ⟨trivial, trivial⟩,
     .cons (.answer (tin := natTy) (tout := unitTy) answer
-      (fun _ _ => TypedProg.pure (ty := unitTy) ⟨trivial, trivial⟩)) (.nil unitTy),
+      (fun _ _ _ _ => TypedProg.pure (ty := unitTy) ⟨trivial, trivial⟩)) (.nil unitTy),
     ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
 
 theorem typed : OldTypedState (rootProgram : ProgramSource) unitTy world machine := by
@@ -1753,8 +1753,8 @@ theorem typed : TypedState (rootProgram : ProgramSource) unitTy world machine co
         cases declared
         apply savedPosition_of_saved
         exact ⟨unitTy, TypedProg.pure (ty := unitTy) ⟨trivial, trivial⟩,
-          .cons (.resume (tin := unitTy) (tout := unitTy) .onSuccess callback (fun ex _ _ => callback_typed world ex)
-            (fun _ typed _ => typed)) (.nil _),
+          .cons (.resume (tin := unitTy) (tout := unitTy) .onSuccess callback
+            (fun w' _ ex _ _ => callback_typed w' ex) (fun _ _ _ typed _ => typed)) (.nil _),
           ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
       · intro p hp; cases hp
       · intro v hv; cases hv
@@ -1793,8 +1793,8 @@ theorem old_typed : OldTypedState (rootProgram : ProgramSource) unitTy world mac
         cases declared
         apply oldSaved_of_saved
         exact ⟨unitTy, TypedProg.pure (ty := unitTy) ⟨trivial, trivial⟩,
-          .cons (.resume (tin := unitTy) (tout := unitTy) .onSuccess callback (fun ex _ _ => callback_typed world ex)
-            (fun _ typed _ => typed)) (.nil _),
+          .cons (.resume (tin := unitTy) (tout := unitTy) .onSuccess callback
+            (fun w' _ ex _ _ => callback_typed w' ex) (fun _ _ _ typed _ => typed)) (.nil _),
           ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
       · intro p hp; cases hp
       · intro v hv; cases hv
```

2. The plan's "monotonicity of every owner predicate of `preds` declared" (§0 item 4; row 87's
   transport), for `SavedOk`: proved as `Test.Program.FramesNotKripke.preds_savedOk_mono`; the
   ledger declaration, for `Assembly.lean`:

```lean
theorem preds_savedOk_mono (root : ProgramSource) (w w' : World) (e : Expect) (x : RSaved) :
    ProofGraph.Obligation (w.leHost w' → (expectOf w e).isSome = true →
      (preds root).SavedOk w e x → (preds root).SavedOk w' e x) := ⟨⟩
```

3. For wave 2's `loop` arm, once `ScopeState.closed.exit` is un-refused: `theorem
   storeTyped_of_typedState … : TypedState root rootTy w m commands → StoreTyped w` (from
   `WorldValid`'s coverage and `state`, the generated `HeapCell` column, and the closed-exit
   column; reading).
4. `Typed/Residual.lean`'s `deferredCompleteWith` pre mirrors `CompletionStrong`
   (`Assembly.lean:38`, its `ofRefGet` arm at `:40`, which row 137 moves to `subN`); this seat's arm
   moves with seat A's `World.lean:81` (seat A item 6).
5. These batteries build typed states through definitions seat C restates, so they need the
   matching edits when the `J`/`I` split lands: `FramesNotKripke.lean` (`typed_of`,
   `afterGood_typed` and the queue proofs read `TypedState`, `QueueOk` (which `Old.StepPreserves`
   also reads), `savedPosition_of_saved`, and the generated `RStateOk` skeleton, whose stores component ends in
   `trivial` while `closed.exit` is refused; reading) and `ProtocolPosts.lean` (`AwaitLoad.OldLoaded` reads `preds`,
   `expectOf`, `RStateOk`). `Old.*` carries its own inert-code predicate already.

## Lines for the coordinator's files

`docs/core/decisions.md` (to append to each row's status):
- **Row 87**: "Frames (row 135) landed by seat B (`074f03ff`): `frameAccepts_mono` and
  `stackAccepts_mono` with no premise on the program judgment, the exit judgment or the hooks;
  `savedOk_mono` and `typedProg_mono` proved; `M3bWorld` 0 open, 5 proved. `(preds root).SavedOk`
  is monotone at a position the world declares (`preds_savedOk_mono`, proved in
  `Test/Program/FramesNotKripke.lean`; ledger line in receipt-B for seat C); the other owner
  predicates of `preds` remain to declare."
- **Row 106**: "The await-by-value post now follows the token rule (seat B, `894e7512`):
  `exitOf ty.answer ty.error`; `awaitValue_frame` proves the saved `seqR` frame accepts the type
  the observer delivers, `awaitValue_delivered` that the delivered value is in the post."
- **Row 117**: "Not touched. The frame arms it amends are now closed under later worlds (row 135):
  the presence clause and the side condition must be stated over `∀ w', w.leHost w' → …`."
- **Row 135**: "Landed (seat B, `074f03ff`, `69063460`): `FrameAccepts`, the three hook protocols and
  `HookLaws` closed under later worlds; the walk restated in place; `hookLaws_interpR` re-proved;
  `stackAccepts_mono`, `savedOk_mono`, `typedProg_mono` proved in `M3bWorld` (0 open); the frame
  category laws in `Contracts`; `guard_inv`'s "exactly" is `TypedProg.guard_frame`. Wrapping at the
  frame refuted (`output_not_kripke`, `hookLawsX_refused`). `E4-TYPED-CE-012` repaired."
- **Row 136**: "Landed (seat B, `894e7512`, `1e75eb16`): the posts at the machine's answers;
  `refModify`/`refModifySome` pre at `RefDeclared w cell .nat`; scope liveness on the scope rows;
  `deferredCompleteWith`'s pre types its completion (found: the old pre admitted a completion no
  later world types). The handler rule proved: `storeStep_typed`, `answerFrame_typed`,
  `seqFrame_typed`; `M3bAdequacy` 8 open, 66 proved, 74 total (open: six `f.total` ref rows, need
  `fits_nat_irrel`; `memoGet`, `memoComplete`, need a memo-table typing clause). Owner decision
  owed on the close rows: the exact post is not fulfilled for a lone finalizer outside
  `⟨unit, never⟩` (`lone_release_outside_post`) nor by the walk through reified exits
  (`closeSeq_protocol_refused`); recommended (a) and (a), see receipt-B. The scope rows' pre
  carries scope liveness (the store side of row 139). The admission census walks the machine's
  answers. `E4-TYPED-CE-010`, `-013` repaired."
- **Row 137**: "Seat B's review (`69063460`): Residual's derivation-chosen certificates
  (`asyncPre`'s three arms, `fiberPre`'s `awaitAll`/`raceAll`) kept in `Ty.sub`, verdict in
  `asyncPre`'s docstring; no other Residual entry compares a declared type with a certificate;
  `refModify`'s pre reads `RefDeclared` (seat A's order); the new `deferredCompleteWith` arm
  (`Residual.lean:56`) compares two declarations and moves to `subN` in the same commit as
  `World.lean:81` (seat A)."

`Test/Counterexamples/REGISTER.md` (the cells to replace; each row's other cells stand):
- `E4-TYPED-CE-010`, status: "REPAIRED 2026-10-01 (seat B, `894e7512`); SEEDED 2026-10-01";
  witness: "`Test/Program/ProtocolPosts.lean`: `AwaitValue.delivered_fits_checked`,
  `post_excludes_delivered`, `await_code_refused` (historical, over `oldFiberPost` and
  `OldTypedProg`), `post_admits_delivered`, `await_code_typed` (current);
  `AwaitLoad.root_code_refused`, `typedState_load_false` (historical, over `AwaitLoad.OldLoaded`)".
- `E4-TYPED-CE-012`, status: "REPAIRED 2026-10-01 (seat B, `074f03ff`); SEEDED 2026-10-01";
  witness: "`Test/Program/FramesNotKripke.lean`: `stackAccepts_not_mono`, `step_loop_refuted`,
  `hookLawsX_old`, `output_typed_one_world` (historical, over `Old.*`); `bad_not_kripke_initial`,
  `bad_not_kripke_by_transport`, `hookLawsX_refused` (the closed judgment refuses the frame);
  `output_not_kripke` (wrapping at the frame, refuted); `evaluate_keeps`, `step_loop_good`,
  `good_stack_transports` (green)".
- `E4-TYPED-CE-013`, status: "REPAIRED 2026-10-01 (seat B, `894e7512`) for every row's post and
  pre; the close rows' handler side is open under the two rows below; SEEDED 2026-10-01"; witness:
  "`Test/Program/ProtocolPosts.lean`, sections `StoreUnit`, `Memo`, `Modify`, `Frontier`,
  `CloseScope`, `CloseIter`, `CompleteWith` (each historical control over `oldStorePre`,
  `oldStorePost`, `oldFiberPost` beside its flip); the handler side in
  `src/Effect4/Laws/Program/Typed/Adequacy.lean` (`M3bAdequacy`)".
- Two new rows (ids are the coordinator's; the next free at `e7f9756f` are `E4-TYPED-CE-016`, `-017`):
  | `E4-TYPED-CE-0xx` | SEEDED 2026-10-01 | The close-scope row's handler answers within
  `ExitOk w' (EffTy.pure .unit)` | `Test/Program/ProtocolPosts.lean`: `CloseScope.lone_release_answer`
  (a scope whose lone finalizer is `FinName.release 7 true` closes to that finalizer's typed
  failure), `lone_release_outside_post`, `release_registration_admitted` (the current `scopeAdd`
  pre admits the registration) | owner decision, receipt-B finding 1 |
  | `E4-TYPED-CE-0yy` | SEEDED 2026-10-01 | The close walk is typed at the close-walk row's exact post
  through the iterator protocol | `Test/Program/ProtocolPosts.lean`: `CloseIter.badName_fits`,
  `closeSeq_protocol_refused` (a reified `badName` failure fits `exitOf unit never`, the walk
  halts with it, and `ExitOk` at `⟨unit, never⟩` refuses the halt) | owner decision, receipt-B
  finding 2 |

`Test/Program/H2PartOne.lean` (the H2 battery; no seat holds it in this wave; it reads this seat's
`LoopProtocol`): the one hunk this branch carries, for row 117's restatement to keep:

```diff
diff --git a/Test/Program/H2PartOne.lean b/Test/Program/H2PartOne.lean
index b4859002..4ab4b78f 100644
--- a/Test/Program/H2PartOne.lean
+++ b/Test/Program/H2PartOne.lean
@@ -292,7 +292,8 @@ theorem loop_admitted (src : ProgramSource) (w : W) :
       [.loop name .unit] := by
   apply StackAccepts.cons (middle := outer)
   · apply FrameAccepts.loop
-    exact LoopProtocol.step (tin := inner) (tout := outer) rfl (fun _ h => False.elim h)
+    intro w' _
+    exact LoopProtocol.step (tin := inner) (tout := outer) rfl (fun _ _ _ h => False.elim h)
   · exact StackAccepts.nil outer
 
 theorem input_ok (w : W) : FullExitOk w inner (.failure missing) :=
```

`docs/ARCHITECTURE.md` (the coordinator's map): `Laws/Program/Typed/Adequacy.lean` sits between
`Residual` and `Stack` (imported by `Stack`): the store half of the typed state and the handler
rules. `docs/STATE.md`: "Rows 135 and 136 landed by seat B; owner decision owed on the close rows."

## What is owed

- **Declared, not proved: 8** `M3bAdequacy` goals: `refUpdate`, `refGetAndUpdate`, `refUpdateAndGet`,
  `refUpdateSome`, `refGetAndUpdateSome`, `refUpdateSomeAndGet` (need `fits_nat_irrel`, seat A's
  module) and `memoGet`, `memoComplete` (need a memo-table typing clause: every memo entry's
  Deferred declared at its layer's context and error types; no typed-state clause states it).
- **Owner decisions**: the two close-row findings above.
- **Not stated as goals**, the handler side that belongs to other work: the code the frame-answered
  fiber rows install (`mask`/`scoped` bodies and `gen`/`loop` protocols are M5's denotation lemma;
  race settlement and async registration payloads are seat C's `RacePayload`/registration
  clauses), and the delivered value of `construction` (a typed-state fact).
- **Owed consumption**: the rules are consumed by wave 2's `loop`/`deliver` arms, which have not
  landed. `storeStep_typed` needs `StoreTyped` from the typed state (seat C, item 3 above).
- **Residual's `subN` arms (plan §3, TY-01), after seat A merges**: not done here (no `subN` at
  `bb269fde`). By row 137's ruling and amendment 3 the derivation-chosen certificates stay in
  `Ty.sub` (verdict recorded); the one declared-against-declared entry is the new
  `deferredCompleteWith` arm, which moves with `World.lean:81` (seat A item 6).
- **Bounded evidence**: the source-module theorems are general (every world, store and program).
  The battery controls are kernel theorems about concrete worlds, stores and machines (the
  counterexamples and their positive instances); their machine facts are computed in the kernel by
  `rfl` or `decide +kernel` (`decide +kernel` in `scopeAdd_open_answer`,
  `memoRelease_answers_scope`, `refModify_bool_answer`, `refModifySome_bool_answer`,
  `close_no_finalizer`, `lone_release_answer`, `release_registration_admitted`,
  `result_no_finish`, and for the order fact `Ty.bool.sub Ty.nat ≠ true` in the two
  `*_pre_refuses`). Nothing is host-only.

## Merge with main (amendment 5)

`refactor/phase1-phase3` at `e7f9756f` (seats E and F merged): `git merge-tree --write-tree
refactor/phase1-phase3 a4fc4b48` reports no conflict (tested). None of this branch's files changed
on main; main's `Test/All.lean` additions sit at other anchors. By reading: seat E's
`Typed/Seq.lean` imports `Residual.lean` and uses `TypedProg`'s seven constructors (the
definition is byte-identical to base here; compared) and seat A's `fitsExit_success_iff`,
`fitsExit_failure_iff`, so it elaborates against this branch; seat F's rename
`Denote.ExitOk` → `Denote.ExitHasTy` only removes an overload this branch's `ExitOk` never
resolved to (its first argument is a `Ty`; every use here applies `ExitOk` to a `World` or passes
it where a judgment over worlds is expected); the declaration names added on both sides meet only
at `natTy`/`unitTy`, in separate test namespaces (`Test.Program.TypedProgBindRed`,
`Test.Program.FramesNotKripke`, `Test.Program.ProtocolPosts.*`). Not built merged: the coordinator
re-checks at the merge.
