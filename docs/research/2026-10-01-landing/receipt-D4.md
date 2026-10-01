# Seat D4 receipt: row 151 (a″) and row 117's closed-row premise

Seat D4 of the 2026-10-01 landing, wave 2. Brief: `docs/research/2026-10-01-landing/brief-D4.md`
(main checkout); plan: `plan.md` (§4 rules, §5 measure). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-D4`, branch `seat/D4`, base `2a306b68`. Evidence words:
**proved** (a kernel theorem compiled here, axioms printed), **reproduced** (another seat's
proved fact compiled again here), **tested** (a finite check run here: a build's report, a
`#guard`, a `decide +kernel`, a `grep`), **reading** (source lines read, named), **assumed** (not
run here).

This file is written incrementally: a stop at any point leaves a true record of what was done up
to that point. `file:line` citations are at the commit named in the section's heading.

## The one thing first

**Merging `seat/D4` into main's head `f4881f74` is textually clean but will not build as merged
until six lemmas of seat D3's `Typed/Commands/Bookkeeping.lean` take the finalizer conjunct.**
`git merge-tree --write-tree f4881f74 HEAD` (tested, exit 0): only `Typed/Assembly.lean`
auto-merges, with no conflict. But D3's file, landed on main after this seat's base, reads the
generated scope clause `ScopeStateOk`, whose two open arms this seat extended (row 151 (a″): the
finalizer's typing `FinalizerOk` beside `FinNameOk`): `scopeStateOk_world`, `scopeStateOk_of`,
`scopeStateOk_entries`, `scopeStoreOk_addUnsafe`, `scopeStoreOk_removeFinalizer` and one call in
`link_preserves` (`f4881f74`'s lines 1564, 2239, 2251, 2337, 2352, 2465). The replacement text is
under "Merge" (reading only: not built, since the coordinator stopped the roots build). Against
seat D2's current tip (`5e82aacf`) there are three textual conflicts and one duplicate declaration
that `merge-tree` cannot see: `fits_context_inv`, declared here in `Membership.lean` and by D2 in
`Denotation.lean` with the same statement. One copy has to be deleted.

## Base and head

Base `2a306b68`. Head: the commit that adds this file, on top of `c0e608e4` (step 4). The seat's
commits, in order: `1ba84f74` (step 1), `d1bf339b` (step 2), `1819fc16` (the coordinator's
wording corrections to step 1), `7690c6d2` (step 3), `c0e608e4` (step 4), then this receipt. The
coordinator's stop arrived after step 3 was committed and the producer chain had run. Step 4's
outputs were committed and `dune build` passed. `check-gen` and `check-ocaml` were not run
(see "Owed"), and the roots build was skipped as instructed.

## Work log (incremental)

- Read in full: `brief-D4.md`, `plan.md` (all, §4 and §5), `receipt-D1.md` (all; the row 151 and
  row 117 sections), `receipt-B.md` (findings 1 and 2, the battery table), decisions rows 117, 140,
  151, 156 (ruled text, worktree `docs/core/decisions.md`), `Test/Program/ProtocolPosts.lean`
  (`CloseScope`, the foot's `#guard_msgs (error)` fixtures), the FR-08 record
  (`docs/core/post-phase-c-synthesis.md` §5.6, `docs/UPSTREAM-BACKLOG.md` row `U-01`, the ruling
  note's §4 in the main checkout, `Test/Audit/RuntimeCoverage.lean:282-283`).
- Build state at the base (tested): `LEAN_NUM_THREADS=4 lake build --no-build Effect4.Laws Test.All`
  in the worktree: "All targets up-to-date (744 jobs)".
- Builds run through `seat-D4/scratch/build.sh` and `leanf.sh` (logging wrappers around
  `LEAN_NUM_THREADS=4 lake build <modules>` and `lake env lean -M6144 -DwarningAsError=true
  <file>` in this worktree; one lake at a time).
- The scratch files this receipt cites are tracked under `seat-D4/scratch/`: the wrappers, the
  probes, the axiom and print outputs, the ledger extractions (`logs/ledger-*.txt`), each build
  log's error and completion lines (`logs/build-tails.txt`), and the two merge dry runs
  (`logs/merge-tree.txt`). The full build logs are not tracked; they run up to 864 KB each.

### Step 1: where the void goes (measured before landing)

- **The brief's placement, built and measured** (tested, then moved): the void at the unsafe
  close's lone branch (`storesCloseScopeUnsafe`, `closeScopeUnsafeR`) with
  `Prim.onSuccessConst (finProgram fin exit) (Prim.success Val.unit)` on the frame side and
  `(guardR .onSuccess (denoteFin fin ex)).bind (seqR fun _ => .pure (.success .unit))` on the
  term side. `build.sh s1-a` (Stores, InterpR, Simulation.Hooks, Machine.Handles,
  Guard.FrameOwned, Typed.Adequacy): exit 0, 372 jobs; `build.sh s1-b Effect4 Effect4.Laws`:
  exit 0, 555 jobs. `build.sh s1-c` (19 test modules that compute or type scope closes): exit 1
  at `Test/Program/RuntimeRContract.lean:955-958` only. Those four `#guard`s pin rc.112's host
  operation counts (`probes/p3-d4/host-d4c.json`, budget 2048) for the source-repairs §20 rows;
  re-evaluated (`seat-D4/scratch/RRCounts.lean`, the file with the four `#guard`s as `#eval`s,
  exit 0): `frameCount`/`termCount` `[[8, 1], [21, 4], [38, 4, 4], [18, 4, 4, 6, 6]]` (host
  `[[8, 1], [19, 4], …]`), `frameCmds`/`termCmds` `[some 17, some 42, some 74, some 75]` (host
  `some 40` for the second row). Only `seqOne` moved: a `scoped` region whose one finalizer is
  closed at the region's exit.
- **Why** (reading): the unsafe close is shared. Rc.112's `scoped` calls `scopeCloseUnsafe`
  directly from its `onExitPrimitive` finalizer (`internal/effect.ts:3937-3947`, `:3945`), and
  so do the machines: the frame's scoped-exit callback (`Program/Compile.lean:1641`, installing
  `finalizerCode interp exit (embed code)`) and the term's `prepareScopedExitR`
  (`Laws/Program/EvaluateR.lean:316`, installing `finalizerR ex code`). There the finalizer's
  value is discarded by the `OnExit` restore, and no rc.112 type promises `void`: only
  `scopeClose` is declared `Effect<void>` (`Scope.ts:567` over `:3775-3776`). Voiding at the
  unsafe close therefore changes no value at a `scoped` exit but adds two counted operations to
  every `scoped` region that closes one finalizer, the commonest resource shape: a second,
  unruled departure from rc.112 (its operation counts, which the machines model for the
  2048-operation yield), against the ruling's "the divergence once", and the brief's docstring
  sentence ("voided here where rc.112's type promises it") would be false at that site.
- **Landed instead** (the ruling's stated place, `Scope.close`, where `Scope.ts:567` promises
  `void`): `storesCloseScope` and `closeScopeR` read the snapshot and void the lone finalizer
  (none → `void`, as `?? void_`; lone → the voided program; two or more → the walk, which
  answers `void` already through `exitAsVoidAll`, `:3826`); the unsafe close is rc.112's again,
  for the `scoped` exit. `RuntimeRContract`'s host counts stand unchanged under this placement
  (tested below).

### Step 1 landed, commit `1ba84f74`

- **Measured before** (reading and tested at the base): `Scope.close` installs the lone
  finalizer's program as is (`closeScopeR` = `closeScopeUnsafeR`'s program or void, the base's
  `InterpR.lean:166-169`; frame `storesCloseScope`, `Stores.lean:1929-1932`); the battery's
  `lone_release_answer` (the failing release closes to `pure (failure (fail 7))`),
  `lone_release_outside_post`, `release_registration_admitted`, `foreign_untyped` hold (the base
  build replayed them, 744 jobs up to date). rc.112 itself (tested, bun 1.4.2 on the pinned
  source, `seat-D4/VendorScopeCloseProbe.ts`, `vendor-scope-close.json`): `Scope.close` answers
  `5` for a lone release answering `5` in the inline slot (`:3788-3789`) and in a one-entry map
  (`:3794-3795`), `undefined` with none or two, and passes a lone release's defect through.
  Effect 3.21.2 (tested, `Effect3ScopeCloseProbe.ts`, a local install outside the repository)
  answers `undefined` in every row: its `close` maps every finalizer count above zero through
  `exitAsVoid` (`fiberRuntime.js:1885-1904`, reading).
- **What moved.** Frame (`Machine/Stores.lean`): `storesCloseScope` reads `scopeCloseSnapshot`
  and installs void / `Prim.onSuccessConst (finProgram fin exit) (Prim.success Val.unit)` / the
  walk; `storesCloseScope_unsafe` (new: `Scope.close` writes the unsafe close's state);
  `storesCloseScope_state_first` and `storesCloseScope_unknown` (census witnesses) re-proved with
  `simp only` lists (`simp?`'s, tested). Term (`Laws/Program/InterpR.lean`): `closeScopeR` the
  same over `(guardR .onSuccess (denoteFin fin ex)).bind (seqR fun _ => .pure (.success .unit))`.
  The unsafe closes are unchanged in code; their docstrings now say the `scoped` exit reads them as
  rc.112 does. Simulation (`Simulation/Hooks.lean`): `voidedFin_means` (new: the two voided lone
  closes are `CodeMeans`-related, through `CodeMeans.onSuccessConst` over `denoteFin_means`, no
  `Delivers` obligation arising: the constant continuation is `CodeMeans.success`),
  `closeWalk_means` (new: the walk arm factored out of `closeScopeUnsafe_means`, which now uses
  it), `closeScope_means` re-proved over the snapshot. `denoteFin_means` and
  `foreignRelease_intro` are untouched (the void is not inside `denoteFin`).
  Consumers re-proved: `Machine/Handles.lean` (`programKeys_voided`, `storesCloseScope_keys` new;
  `stores_keyBounded`'s `closeScope` field through it), `Guard/FrameOwned.lean`
  (`raceSites_closeScope` over the snapshot), `Guard/NativeState.lean` (`closeScope_state`),
  `Guard/MemoIds.lean` (`closeScope`), `Simulation/Actions.lean` (`storesOk_closeScope`), each
  of the last three through `storesCloseScope_unsafe` (one `obtain` each). Typed
  (`Typed/Adequacy.lean`, which now imports `Typed/Seq.lean`): `voidedClose_typed` (new: a
  finalizer typed at `⟨unknown, never⟩` closes, voided, at `⟨unit, never⟩`, by `seq_typed`);
  `closeScope_installs`' `lone` premise weakened from `⟨unit, never⟩` to `⟨unknown, never⟩`
  (its ledger line `M3bAdequacy.closeScope_installs` restated in the same commit).
- **Controls** (`Test/Program/ProtocolPosts.lean`, `CloseScope`): `lone_release_answer` restated
  over the control-erased code (`eraseControl`: the failing release's failure passes through the
  void; `decide +kernel`, `[propext]`); `close_one_typed` re-proved (one term:
  `live_of_keys_nil rfl` for `Live w unit`); new run control `closeLone` (`scoped(acquireRelease
  (succeed 1, … => succeed 5) >> Scope.close(scope, exit(void)))`, the scope read back through
  the `Scope` service): `#guard`s that the checker types it `⟨unit, never, ∅⟩` and that the frame
  machine (`Api.replay`) and the term machine (`replayR`) both exit `success unit` at fuel 200
  (tested); rc.112 answers `5` on the same shape (row `inline` above).
- **Divergence record** (the FR-08 form): `docs/UPSTREAM-BACKLOG.md` row `U-02` (finding, rc.112
  lines, Effect 3 comparison, reproduction, disposition, suggested upstream fix, not reported);
  the evidence folder `docs/research/2026-10-01-landing/seat-D4/` (`README.md`, the two probes,
  their outputs, `vendor-sha256.json`, whose `Scope.ts` and `internal/effect.ts` hashes equal the
  runtime census's `input` lines); the docstrings of `storesCloseScope` and `closeScopeR` name
  `Scope.ts:567`, `internal/effect.ts:3775-3776`, `:3788-3789`, `:3794-3795` and `U-02`. Not done
  here (proposed below): the runtime census row and the truth-harness fixture, U-01's other two
  records.
- **Commands and results** (tested): `build.sh s1-e Effect4 Effect4.Laws`: exit 0, 555 jobs,
  1064 s (the whole cone below `Machine/Stores.lean`); `build.sh s1-f` (`Test.Program.
  ProtocolPosts` and the 19 test modules that compute or type scope closes, among them
  `RuntimeRContract`, whose four host-count `#guard`s pass unchanged, `Machine.Fuzz`,
  `ScopeContract`, `AgreementContract`, `DenoteRContract`, `Audit.RuntimeCoverage`): exit 0, 427 jobs;
  `build.sh s1-g Effect4.Machine.Stores Effect4.Laws.Program.InterpR` after the last docstring and
  `simp only` edits: exit 0, 238 jobs. Axioms (`seat-D4/scratch/AxiomsStep1.lean`, `lake env lean`,
  exit 0), 20 theorems: `storesCloseScope_unsafe`, `storesCloseScope_state_first`,
  `storesCloseScope_unknown`, `programKeys_voided`, `FrameOwned.raceSites_closeScopeUnsafe`
  `[propext]`; `storesCloseScope_keys`, `storesCloseScopeUnsafe_keys`, `stores_keyBounded`,
  `closeWalk_means`, `closeScopeUnsafe_means`, `voidedFin_means`, `closeScope_means`,
  `storesOk_closeScope`, `FrameOwned.raceSites_closeScope`, `FrameOwned.closeScope_hook_sites`,
  `voidedClose_typed`, `closeScope_installs`, `NativeState.closeScope_state`,
  `MemoIds.closeScope` `[propext, Quot.sound]`; the battery's `lone_release_answer` `[propext]`,
  `close_one_typed` `[propext, Quot.sound]` (printed by the build).

### Step 2: finalizers typed by a source row; the registration pre; the flips

- **Measured before** (tested and reading, at `1ba84f74`): the scope store's generated typing
  reads `FinNameOk` at each registered finalizer, which is `True` at every name but `foreign`
  (`CaptureOk`) (printed, `seat-D4/scratch/PrintGen.lean`); `Preds` has 11 fields and no defaults
  (the emitter writes `structure Preds (W : Type) where …` with bare binders,
  `Typed/TypedStateDecl.lean` at its `bundle`); the edge census (`#edge_census`, tested) reaches
  `FinName` at three fields: `ScopeState.openInline.finalizer`, `ScopeState.openMap.entries`
  (through `List`, `Prod.2`) and `MemoEntry.finalizer` (a memo entry's metadata, always
  `memoEntry layer memoMap`, never registered from there). No existing source kind could state a
  predicate at the two scope fields and keep the walk to `FinNameOk`: an `owner` row must name a
  structure or constructor and covers its subtree (so `Capture`'s own owner row would become a
  duplicate, `TypedSources.ownerCoverage`), and a `custom` row covers its field's subtree too (the
  capture clause would vanish at registered finalizers) and types the whole field (two predicates,
  one per field type). The registration pre cannot mention the program judgment: `storePre` is a
  premise of `TypedProg`'s own `store` constructor (through `Ψ_S`).
- **The `Preds` instances, counted** (tested, `grep` of every instantiation of the production
  bundle): three set every field explicitly (`Typed/Assembly.lean` `preds`,
  `ValueMembership.lean` `Reviewed.preds`, `Test/Audit/TypedStateDecl.lean` `readsMetadata`, the
  last missing from receipt D1's list); the other eight sites (`M6Capstone.lean` ×5, `H1Shapes.lean`,
  `FramesNotKripke.lean`, `ProtocolPosts.lean` `oldStatePreds`) are `{ preds root with … }`
  updates, which inherit a new field. So the new field costs one line in `src` and two in `Test`.
  Judgment on a generator default (the coordinator's question): not taught. A default on a
  generated invariant field lets any instance, production `preds` included, omit the clause with
  no error, against the generator's "no silent field drop" rule (post-Phase C synthesis §6.B), to
  save two one-line edits.
- **What moved** (commit `d1bf339b`). *The row.* A new source kind `Source.each (pred)`
  (`Typed/Vocabulary.lean`; decoded in `Typed/TypedSources.lean`, labelled in
  `Typed/PositionGate.lean`, emitted in `Typed/TypedStateDecl.lean`): on a containment edge with
  one child type, the hand predicate at each child the field holds, through the edge's wrappers,
  beside the child's own clause; it covers nothing; a field with two child types or a direct
  position is refused. Two rows in `Typed/Sources.lean`, `("Effect4.ScopeState.openInline.
  finalizer", .each "FinalizerOk")` and `("Effect4.ScopeState.openMap.entries", .each
  "FinalizerOk")`, beside the capture row and the scope-exit row. Printed (tested): `Preds` gains
  `FinalizerOk : W → Expect → FinName → Prop` (12 carrier predicates); `ScopeStateOk`'s open arms
  read `P.FinalizerOk w e finalizer ∧ FinNameOk P w e finalizer` and `(∀ v0 ∈ entries,
  P.FinalizerOk w e v0.2) ∧ ∀ v0 ∈ entries, FinNameOk P w e v0.2`; `MemoEntryOk` is unchanged
  (the memo entry's finalizer name is not a registration). The pin `Typed/State.lean:24` is
  re-pinned: "17 predicates, 12 carrier predicates, 1 refusals"; `Test/Audit/PositionCensus.lean`'s
  gate report "85 positions from 4 roots, 88 source rows" (the two edge rows; the per-position
  kinds unchanged). `docs/GENERATED.md` names the kind.
  *The clause* (`Typed/Adequacy.lean`): `FinalizerTyped root w fin := ∀ w', w.leHost w' → ∀ ex,
  FitsExit w' ⟨unknown, unknown, ∅⟩ ex → TypedProg root w' ⟨unknown, never, ∅⟩ (denoteFin fin
  ex)`, the bundle's `FinalizerOk` (`preds`, `Typed/Assembly.lean`). **Which clause and why:**
  the weaker clause, quantified over the closing exits that fit rc.112's release parameter type
  `Exit<unknown, unknown>` (`internal/effect.ts:3973`, the type the closed-scope row already gives
  a scope's exit, `ScopeExitOk`): a foreign finalizer's release reads its exit at that type
  (`capture_lookup`'s premise), so no foreign finalizer is typed at an exit outside it (an exit
  with a dangling handle or a shape defect), and the close needs no more. World transport:
  `finalizerTyped_mono`, declared and proved in `M3bWorld` (row 87; the scope's report at
  `Assembly.lean`'s foot reads 0 open, 7 proved, 7 total).
  *The pre* (`Typed/Residual.lean`): `storePre`'s `scopeAdd scope fin` arm is `ScopeLive w scope ∧
  FinalizerAdmitted root w fin`, where `FinalizerAdmitted` reads a finalizer by name: `foreign c`
  → `CaptureTyped root w c` (moved from `Typed/Assembly.lean` to `Typed/Admission.lean`, its
  statement unchanged, so the pre can read it), `release _ fails` → `fails = false`,
  `closeChildScope`/`closeChildOnFailure` → `ScopeLive` of the child, `detachFromParent` →
  `ScopeLive` of the parent, every other name `True`. The pre reads the admission, not the clause:
  `storePre` is a premise of `TypedProg`'s own `store` constructor (through `Ψ_S`), so it cannot
  mention `TypedProg`. `finalizerAdmitted_mono` and `captureTyped_rows_append` (new) keep
  `storePre_mono` and `storePre_rows_append` proved; `scopeAdd_implements` reads `pre.1`.
  *The bridge* (`Typed/Assembly.lean`): **`finalizerTyped_of_admitted`**: a finalizer the pre
  admits is typed at every later world and fitting exit; the synthetic names by their programs
  (`interruptFiber`, `awaitNewChildren`: a void-answering fiber row; `closeChildScope`,
  `closeChildOnFailure`: the close row at a present scope, its post below `⟨unknown, never⟩` by
  `exitOk_finalizer`; `detachFromParent`, `memoDone`: a void-answering store row; `parkThen`: the
  host slot's `async` at the finalizer type; `memoEntry`: `seq_typed` at `unit | Scope`, the layer
  scope's presence read back by `fits_scope_inv`), the foreign one through the context read
  (`fits_context_inv`, new in `Membership.lean` beside `fits_option_inv`), the context restore,
  the construction query and the masked release at the point the checker types it
  (`capture_release`, new: `capture_lookup` with the release's error column normalizing to
  `never`, from `Checker.inv_acquireRelease`; `capture_lookup` is now its corollary, statement
  unchanged). The store's typing at J: `scopeFinalizers_typed` (the generated clause gives
  `FinalizerTyped` at every finalizer of a scope's close order) and `finalizers_of_typedState`
  (`MachineTyped` gives it for every scope of `w.state`).
  *The close* (`Typed/Adequacy.lean`): `closeScope_installs` takes `fins : ∀ entry ∈
  st.scopes.entries, ∀ fin ∈ entry.scope.closeOrder, FinalizerTyped root w fin` and `exitFits :
  FitsExit w ⟨unknown, unknown, ∅⟩ exit` in place of `lone`; the ledger line
  `M3bAdequacy.closeScope_installs` restated the same (still proved; the scope's report 2 open,
  72 proved, 74 total, unchanged). `lone_of_snapshot` (new) reads the lone finalizer off the
  scope.
- **The `Preds` instances edited**: `Typed/Assembly.lean` `preds` (`FinalizerOk w _ fin :=
  FinalizerTyped root w fin`), `Test/Counterexamples/Machine/Semantics/ValueMembership.lean`
  `Reviewed.preds` (`FinalizerOk _ _ _ := True`, absent when that judgment was reviewed),
  `Test/Audit/TypedStateDecl.lean` `readsMetadata` (`FinalizerOk := fun _ _ _ => True`). The eight
  record updates compiled unchanged (tested: the cone build). `StaleCode.lean`'s
  `scopeStateOk_tr` re-proved at the two open arms (one anonymous constructor each).
- **Controls** (`Test/Program/ProtocolPosts.lean`, `CloseScope`). Flipped to red:
  `release_registration_admitted` is history as `old_release_registration_admitted` over
  `OldScopeAddPre` (the base's pre, kept local); **`release_registration_refused`**: `¬ storePre
  root w (.scopeAdd 0 (.release 7 true)) cert` at every root, world and certificate; the base's
  proof script pinned failing against the current pre by a `#guard_msgs (error)` fixture
  ("'change' tactic failed, pattern (w.state.scopes.entryAt 0).isSome = true is not
  definitionally equal to target storePre root w (SyncOp.scopeAdd 0 (FinName.release 7 true))
  cert"); **`failing_release_untyped`**: `¬ FinalizerTyped root w (.release 7 true)` (at the
  closing exit `void` its program answers `Fail 7`). Positive: `lone_release_outside_post` stands
  as a fact (the failing release answers outside the post) whose shape no typed state holds now;
  the lone typed finalizers close within the post: `close_one_typed` (a succeeding `release`,
  through the store's typing and `finalizerTyped_of_admitted`), and the value-answering capture's
  closing corollary **`foreign_close_typed`** (the scope holding the `5`-answering capture, closed,
  installs a program typed at `⟨unit, never⟩`), with **`foreign_typed_unknown`** (that capture's
  own program is typed at `⟨unknown, never⟩`) beside `foreign_untyped` (typed at no type whose
  answer is `unit`, unchanged) and `acq_capture_typed` (its `CaptureTyped`); `close_zero_typed`,
  `close_two_typed` re-proved through the store's typing; helpers `failed_fits`, `zero_fins`,
  `one_fins`, `two_fins`, `foreign_fins` (`decide +kernel`). **Finding** (red):
  `closeScope_pre_admits_unfit_exit`: at a world whose store holds the open scope 0 the code
  `closeScope 0 (die badName)` is typed (the close-scope pre reads the scope's presence only),
  while the closed-scope clause refuses that exit at every world: the step leaves no typed store
  (below, owed).
- **Commands and results** (tested): `build.sh s2-a Effect4.Laws.Program.Typed.State`: exit 1 at
  the pin (the expected 11 → 12), then `s2-b` exit 0; `s2-c` exit 1 at `Residual.lean:829, :831`
  (a local name shadowing the section's `hsvc`), `s2-d` exit 1 at `Assembly.lean:913, :916`
  (`exitOk_finalizer`'s implicit types and `rfl` on `Ty.sub`), `s2-e` exit 0 (385 jobs); `s2-f
  Effect4 Effect4.Laws` exit 0 (555 jobs); the test cone (the 38 Test modules importing a changed
  typed module, computed from the import graph, `seat-D4/scratch/cone2.txt`): `s2-g` exit 1 at
  `ProtocolPosts.lean` only (an expected type with `root` free in a `decide`, and the fixture's
  placeholder message), `s2-h` exit 0, 599 jobs. Axioms (`seat-D4/scratch/AxiomsStep2.lean`, exit 0),
  20 theorems at `[propext, Quot.sound]`: `fits_context_inv`, `finalizerAdmitted_mono`,
  `captureTyped_rows_append`, `storePre_mono`, `storePre_rows_append`, `typedProg_rows_append`,
  `typedProg_mono`, `finalizerTyped_mono`, `lone_of_snapshot`, `closeScope_installs`,
  `scopeAdd_implements`, `scopeFinalizers_typed`, `finalizers_of_typedState`, `capture_release`,
  `capture_lookup`, `exitOk_unit_finalizer`, `exitOk_finalizer`, `finalizerTyped_of_admitted`,
  `storeTyped_of_typedState`, `voidedClose_typed`. Battery (printed by the build):
  `release_registration_refused`, `failing_release_untyped`, `acq_capture_typed`,
  `foreign_typed_unknown`, `failed_fits`, `foreign_close_typed`, `closeScope_pre_admits_unfit_exit`,
  `close_zero_typed`, `close_one_typed`, `close_two_typed` `[propext, Quot.sound]`;
  `old_release_registration_admitted`, `zero_fins`, `one_fins`, `two_fins`, `foreign_fins`,
  `oneScope_live`, `lone_release_answer` `[propext]`.
- **The ledger.** No `#proof_wanted`/`#obligation_proved` line read `closeScope_installs`' `lone`
  premise except its own (`M3bAdequacy.closeScope_installs`, restated here). In seat D3's branch
  (`seat/D3`, read with `git show`, not merged here) no command proof reads `closeScope_installs`;
  its `Commands/Bookkeeping.lean` reads the generated scope clause the row changes (see "Merge").
- **`E4-TYPED-CE-016`**: repaired (the register line is proposed below).

### The coordinator's review of step 1, commit `1819fc16`

The coordinator accepted the placement at `Scope.close` (Codex's static review of `1ba84f74` found
no defect) and amended the brief and row 151 to the landed site. Its two wording corrections, and
one more of the same kind found while making them: `voidedClose_typed`'s docstring
(`Typed/Adequacy.lean:1200`) named `closeScopeUnsafeR` and now names `closeScopeR`; the Effect 3
comparison (`seat-D4/README.md`, the probe's header, `U-02`'s comparison cell) names the three rows
it ran (`zero`, `inline`, `two`; not `mapOne` or `loneDie`); `ProtocolPosts.lean`'s foreign-capture
section docstring said the close installs the finalizer's program as is (true before (a″)) and now
says what held before and what holds since. Build (tested): `build.sh s2-fix
Effect4.Laws.Program.Typed.Adequacy Test.Program.ProtocolPosts`, exit 0, 387 jobs; the Effect 3
probe re-run (tested) prints the committed `effect3-scope-close.json` byte for byte.

### Step 3: row 117's closed-row premise, commit `7690c6d2`

- **Measured before** (reading, `Typed/Assembly.lean` at `1819fc16`): `LoadsTyped` (`:1047`) and
  `ReachableTyped` (`:1061`) end `ClosedEff rootTy → …`; `M7Fragment` (`:1469`) has `lawful`,
  `emptyTable`, `checked`, `closed`, `answerFree`; `DecisionKeeps` (`:1052`) quantifies over
  machines already in `J`. Consumers (tested by `grep` over `src/` and `Test/`):
  `loadsTyped_of_denotesTyped`, `reachable_of_ledger`, `m7_of_capstone` (and `m7_of_ledger` through
  them) in `src`; `FitsOrder.lean`, `AwaitLoad.lean`, `RawOrderLoad.lean`, `LayerRefs.lean` in
  `Test`. Every control's root type has the empty requirement row (`FitsOrder.rootTy3` is
  `⟨…, .never, Requirement.empty⟩`, `AwaitLoad.rootTy` and `LayerRefs.rootTy` are `EffTy.pure _`),
  so no refutation became vacuous (the refutations supply the premise by `rfl`).
- **The statements changed (one hunk each)**:
  1. `LoadsTyped`: `… → ClosedEff rootTy → rootTy.requires = Env.Requirement.empty → ∃ w,
     MachineTyped root rootTy w (loadR root.program fuel compileFuel)`.
  2. `ReachableTyped`: `… → ClosedEff rootTy → rootTy.requires = Env.Requirement.empty →
     RReachable root fuel m → ∃ w, MachineTyped root rootTy w m`.
  3. `M7Fragment`: the field `closedRow : rootTy.requires = Env.Requirement.empty` after `closed`
     (M7a–c read the fragment, so their three statements carry it).
  `DecisionKeeps` unchanged. Docstrings cite rc.112 `Effect.ts:17494-17497` (`runPromise` takes
  `Effect<A, E>`, whose requirement parameter is `never`; an open row runs only through
  `runPromiseWith`, `:17533-17535`, by receipt D1's reading).
- **The consumers re-proved, with the one-line change each needed**:
  `loadsTyped_of_denotesTyped` (`intro _ checked closed` → `intro _ checked closed _`);
  `reachable_of_ledger` (`rintro lawful checked closed row ⟨tape, free, rfl⟩` and `load lawful
  checked closed row`); `m7_of_capstone` (passes `fragment.closedRow`); `m7_of_ledger` unchanged
  (its term goes through the two above). Tests: `FitsOrder.Reviewed.loadsTyped_false` (`h src.lawful
  prog3_typed rootTy3_closed rfl`), `FitsOrder.capstone_implies_load` (`fun lawful h1 h2 h3 => cap …
  lawful h1 h2 h3 …`), `FitsOrder.loadsTyped` (`fun _ _ closed _ => …`), `FitsOrder.capstone_at_load`
  (`fun lawful checked closed row _ => loadsTyped lawful checked closed row`), `AwaitLoad.loadsTyped`
  and `AwaitLoad.capstone_at_load` (the same two), `RawOrderLoad.capstone_false` (`… rootTy3_closed
  rfl (rreachable_load src 100)`); `LayerRefs.loadsTyped` unchanged (through
  `loadsTyped_of_denotesTyped`). No proof uses the premise: part two (the presence clause) stays
  open, `E4-TYPED-CE-008` stays SEEDED.
- **Commands** (tested): `build.sh s3-a Effect4.Laws.Program.Typed.Assembly` and the 38-module
  test cone: exit 0, 599 jobs, first try; `build.sh s3-b Effect4.Laws`: exit 0, 541 jobs. Ledger
  printed (unchanged counts, changed meanings): `M3bAssembly` 3 open / 1 proved / 4,
  `M6Ledger` 20 / 0 / 20, `M7` 4 / 0 / 4, `M3bWorld` 0 / 7 / 7. Axioms
  (`seat-D4/scratch/AxiomsStep3.lean`, exit 0): the four `src` theorems and the eight test theorems
  above, every one `[propext, Quot.sound]`.

### Step 4: the producer chain and the OCaml face, commit `c0e608e4`

- **Measured before** (reading). Step 1 changed `Machine/Stores.lean`, which is under the `Effect4`
  root. The LCNF cut of that root is `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml`, with
  their closure tables (`docs/GENERATED.md`, the `lcnf` inputs). Step 2's generator change
  (`Typed/TypedStateDecl.lean` and the new source kind) is under `Effect4.Laws`. No producer group
  reads it: the `#typed_state` command runs at elaboration.
- **Commands** (tested). The chain ran through `seat-D4/scratch/chain.sh`, each step with
  `LEAN_NUM_THREADS=1`, logging its exit code, in the fixed order. First `build.sh s4-tools` built
  the chain's generator tools (among them `OCaml5.Tools.EffGen`, `EffWire`, `CasGoldens` and
  `Drivers.TsGen`): exit 0, 132 jobs. Then:
  - `python3 scripts/generate.py --only derived`: exit 0, 163 s, no file changed.
  - `--only lcnf`: exit 0, 92 s, four files changed: `ocaml/engine/api_engine.ml`,
    `ocaml/gen/api_gen.ml`, `ocaml/gen/closure-api_engine.tsv` and
    `ocaml/gen/closure-api_gen.tsv`. `fibers_gen.ml`, `machine_gen.ml` and their tables were
    unchanged.
  - `--only eff`: exit 0, 9 s. `--only wire`: exit 0, 7 s. `--only cas`: exit 0, 5 s. None of
    these three changed a file (`git status` after each step, `seat-D4/scratch/logs/chain.summary`).

  Then `(cd ocaml && opam exec --switch=effect4 -- dune build)`: exit 0, 20 s, no output.
- **What moved** (tested, the diff). `stores_close_scope` now reads `scope_close_snapshot`. It
  answers `Prim_success Val_unit` when the scope holds no finalizer,
  `Prim_onSuccessConst (fin_program head exit_, Prim_success Val_unit)` when it holds one, and the
  walk when it holds more. Its closure row grows from 8 to 13 nodes. `stores_close_scope_unsafe`
  keeps its closure hash (`312252404442827136`); only its place in the file moved. The other
  changed rows are reorderings. The four files are committed by explicit paths and were never
  edited by hand.
- **Not run.** The coordinator's stop, 2026-10-01, said "no new steps from here; … skip the roots
  build". So the `ts` and `readme` groups, `make check-gen` and `make check-ocaml` did not run. The
  exact obstacles:
  - `check-gen` goes through `gen-hermetic`. Its `variances` and `derived` rules and the corpus
    index all depend on `| build`, which is `lake build`, the full build the coordinator runs at
    the merge.
  - The `readme` rule depends on `| ts/eff/node_modules`. That directory is missing in this
    worktree, and its recipe is `bun install --frozen-lockfile`, a package download. This was not
    attempted; no permission was asked for or refused.
  - `check-ocaml` depends on `$(CORPUS)/index.tsv`, which depends on `| build`.

  Two assumptions, by reading. No `ts` output reads the machine's close or the typed state (the
  group's inputs are the wire tags, `Codegen/Print.lean` and `tools/`), so it is assumed
  unchanged. The corpus index records the checker's verdicts, and `Program/Checker.lean` is
  untouched, so it is also assumed unchanged.

## The divergence record

It follows FR-08's form (`U-01`):

- `docs/UPSTREAM-BACKLOG.md`, row `U-02`. It records the finding; the rc.112 lines
  (`Scope.ts:567`, `internal/effect.ts:3775-3776`, `:3788-3789`, and `:3794-3795`, the brief's
  `:3795`); the Effect 3.21.2 comparison; the reproduction; the disposition (a signed divergence,
  decisions row 151 (a″)); the suggested upstream fix; and that it has not been reported.
- The evidence, `docs/research/2026-10-01-landing/seat-D4/`: `README.md`, the two bun probes,
  their outputs, and `vendor-sha256.json`. That file's `Scope.ts` and `internal/effect.ts` hashes
  equal the runtime census's `input` lines.
- The docstrings of `storesCloseScope` (`Machine/Stores.lean:1927-1936` at `c0e608e4`) and
  `closeScopeR` (`Laws/Program/InterpR.lean:167-175`).
- The battery: `Test/Program/ProtocolPosts.lean`, `CloseScope` (`closeLone`).

The census row and the truth fixture are owed (see below).

For step 1, the red side was reproduced on rc.112 itself: the bun probe answers `5` for the lone
release (tested). It was not reproduced on this tree's base machine, which was not rebuilt at the
base. There, by reading `Stores.lean:1929-1932` at `2a306b68`, `storesCloseScope` installs
`finProgram fin exit` as is.

## The ledger, before and after

These are the `Effect4.Laws` root's reports: each scope's last "N open, M proved, T total" line in
a build log, read by `seat-D4/scratch/ledger.py`.

| | Scopes | Open | Proved | Total | `M3bWorld` | `M3bAdequacy` | `M3bAssembly` | `M6Ledger` | `M6Edits` | `M7` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Before (base) | 68 | 36 | 418 | 454 | 0 / 6 / 6 | 2 / 72 / 74 | 3 / 1 / 4 | 20 / 0 / 20 | 6 / 7 / 13 | 4 / 0 / 4 |
| After (`7690c6d2`; step 4 changed no Lean) | 68 | 36 | 419 | 455 | 0 / 7 / 7 | 2 / 72 / 74 | 3 / 1 / 4 | 20 / 0 / 20 | 6 / 7 / 13 | 4 / 0 / 4 |

How each row was measured:

- **Before.** Tested at `1ba84f74` (`s1-e`, which rebuilt the whole `Effect4.Laws` cone). This
  equals the base: step 1 adds and removes no ledger line (tested, a `grep` of each seat commit's
  diff for ledger commands; the only one in the seat is step 2's
  `#obligation_proved … M3bWorld.finalizerTyped_mono`).
- **After.** Tested: `s2-f` after step 2 and `s3-b` after step 3 print the same numbers.

The one moved obligation is `M3bWorld.finalizerTyped_mono`, declared and proved (+1 proved, +1
total). `M3bAdequacy.closeScope_installs` is restated and still proved. Step 3 changed the
meanings of `M3bAssembly`'s load goal, `M6Ledger`'s reachability goal and `M7`'s four goals (they
now take the closed-row premise), but not their counts. Main's ledger differs: seat D3 moved the
`M6Ledger`/`M6Edits` reports into the command modules and closed goals there. The merged numbers
are the coordinator's to measure.

## Every changed path

Measured with `git diff --numstat 2a306b68 c0e608e4`, plus this receipt.

- **`src/`**:
  - `src/Effect4/Machine/Stores.lean` (+40 −10)
  - `src/Effect4/Laws/Machine/Handles.lean` (+38 −17)
  - `src/Effect4/Laws/Program/Guard/FrameOwned.lean` (+13 −12)
  - `src/Effect4/Laws/Program/Guard/MemoIds.lean` (+6 −8)
  - `src/Effect4/Laws/Program/Guard/NativeState.lean` (+8 −10)
  - `src/Effect4/Laws/Program/InterpR.lean` (+19 −6)
  - `src/Effect4/Laws/Program/Simulation/Actions.lean` (+5 −8)
  - `src/Effect4/Laws/Program/Simulation/Hooks.lean` (+48 −38)
  - `src/Effect4/Laws/Program/Typed/Adequacy.lean` (+74 −9)
  - `src/Effect4/Laws/Program/Typed/Admission.lean` (+14 −0)
  - `src/Effect4/Laws/Program/Typed/Assembly.lean` (+212 −29)
  - `src/Effect4/Laws/Program/Typed/Membership.lean` (+17 −0)
  - `src/Effect4/Laws/Program/Typed/PositionGate.lean` (+3 −2)
  - `src/Effect4/Laws/Program/Typed/Residual.lean` (+55 −4)
  - `src/Effect4/Laws/Program/Typed/Sources.lean` (+7 −1)
  - `src/Effect4/Laws/Program/Typed/State.lean` (+1 −1)
  - `src/Effect4/Laws/Program/Typed/TypedSources.lean` (+1 −0)
  - `src/Effect4/Laws/Program/Typed/TypedStateDecl.lean` (+14 −2)
  - `src/Effect4/Laws/Program/Typed/Vocabulary.lean` (+5 −0)
- **`Test/`**:
  - `Test/Program/ProtocolPosts.lean` (+251 −24)
  - `Test/Audit/TypedStateDecl.lean` (+50 −0)
  - `Test/Audit/PositionCensus.lean` (+1 −1)
  - `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean` (+2 −2)
  - `Test/Counterexamples/Machine/Semantics/FitsOrder.lean` (+4 −4)
  - `Test/Counterexamples/Machine/Semantics/RawOrderLoad.lean` (+1 −1)
  - `Test/Counterexamples/Machine/Semantics/StaleCode.lean` (+2 −2)
  - `Test/Counterexamples/Machine/Semantics/ValueMembership.lean` (+2 −0)
- **Generated**:
  - `ocaml/engine/api_engine.ml` (+39 −30)
  - `ocaml/gen/api_gen.ml` (+42 −33)
  - `ocaml/gen/closure-api_engine.tsv` (+9 −9)
  - `ocaml/gen/closure-api_gen.tsv` (+9 −9)
- **Docs**:
  - `docs/UPSTREAM-BACKLOG.md` (+1 −0)
  - `docs/GENERATED.md` (+4 −1)
- **Evidence** (force-added):
  - `docs/research/2026-10-01-landing/seat-D4/README.md`
  - `docs/research/2026-10-01-landing/seat-D4/VendorScopeCloseProbe.ts`
  - `docs/research/2026-10-01-landing/seat-D4/vendor-scope-close.json`
  - `docs/research/2026-10-01-landing/seat-D4/vendor-sha256.json`
  - `docs/research/2026-10-01-landing/seat-D4/Effect3ScopeCloseProbe.ts`
  - `docs/research/2026-10-01-landing/seat-D4/effect3-scope-close.json`
- **This receipt**: `docs/research/2026-10-01-landing/receipt-D4.md`.

None of `README.md`, `AGENTS.md`, `docs/core/decisions.md`, `docs/STATE.md`,
`docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md` or `lakefile.toml` was edited. No
root import file and no file of seats D2, D3 or J2 was touched.

## Merge

### Into main's head `f4881f74`

The dry run (tested): `git merge-tree --write-tree --name-only --messages f4881f74 HEAD` exits 0
and prints only "Auto-merging src/Effect4/Laws/Program/Typed/Assembly.lean". It writes objects and
touches no ref or worktree.

Main's commits since the base include seat D3's merge `7d50cfe6` and its follow-up `8c65d527`,
seat W1's merge (`cdd62673`) and probe U's (`b5501b82`). They change 16 Lean files. Four of those read a
declaration this seat added or restated (tested, `git grep` at `69c78069`, which has the same tree
under `src/` as `f4881f74`):

- `Typed/Assembly.lean`. The auto-merge: D3's `QueueOk.links` at `Stores.ScopeLive` and the moved
  `M6Ledger`/`M6Edits` report lines. This seat's hunks are elsewhere in the file.
- `Typed/Commands/Bookkeeping.lean`.
- `Typed/Edits.lean`.
- `Typed/World.lean`, in a comment only.

**`Typed/Commands/Bookkeeping.lean`** (seat D3's, landed) needs six edits. They were not made here
(it is D3's file) and not built (reading). After step 2 the generated `ScopeStateOk` reads:

- at `openInline key fin`: `P.FinalizerOk w e fin ∧ FinNameOk P w e fin`;
- at `openMap entries`: `(∀ v0 ∈ entries, P.FinalizerOk w e v0.2) ∧ ∀ v0 ∈ entries, FinNameOk P w
  e v0.2`.

This is printed in step 2. `(preds root).FinalizerOk w e fin` is `FinalizerTyped root w fin` by
`preds`' field, definitionally (`scopeFinalizers_typed` reads it that way, proved). The edits, at
`f4881f74`'s line numbers:

1. `scopeStateOk_world` (:1564), its two open arms:
   ```lean
   | openInline key fin => exact ⟨finalizerTyped_mono root w w' fin ord h.1, finNameOk_world ord h.2⟩
   | openMap entries =>
     exact ⟨fun v0 hv => finalizerTyped_mono root w w' v0.2 ord (h.1 v0 hv),
       fun v0 hv => finNameOk_world ord (h.2 v0 hv)⟩
   ```
2. `scopeStateOk_of` (:2239) takes a first premise
   `(typed : ∀ v ∈ st.entries, FinalizerTyped root w v.2)`, and its two open arms build the pair:
   ```lean
   | openInline key fin =>
     exact ⟨typed (key, fin) (List.mem_singleton_self _), fins (key, fin) (List.mem_singleton_self _)⟩
   | openMap entries => exact ⟨fun v hv => typed v hv, fun v hv => fins v hv⟩
   ```
3. `scopeStateOk_entries` (:2251): `exact h` becomes `exact h.2` at both open arms. Beside it goes
   a sibling, `scopeStateOk_typed`: the same statement and proof with `FinalizerTyped root w v.2`
   for `FinNameOk (preds root) w e v.2` and `h.1` for `h`.
4. `scopeStoreOk_addUnsafe` (:2337) takes the premise `(finTyped : FinalizerTyped root w fin)`
   after `finOk`, and its `refine` passes three functions:
   ```lean
   refine scopeStoreOk_setEntry h ⟨⟨scopeStateOk_of (fun v hv => ?_) (fun v hv => ?_) (fun ex hex => ?_)⟩⟩
   · rcases entries_addUnsafe entry.scope key fin v hv with oldv | rfl
     · exact scopeStateOk_typed old v oldv
     · exact finTyped
   · rcases entries_addUnsafe entry.scope key fin v hv with oldv | rfl
     · exact scopeStateOk_entries old v oldv
     · exact finOk
   · -- the closing-exit bullet as it stands
   ```
5. `scopeStoreOk_removeFinalizer` (:2352) gets the typed half through the same sublist:
   `scopeStateOk_of (fun v hv => ?_) (fun v hv => ?_) (fun ex hex => ?_)`, whose first bullet is
   `exact scopeStateOk_typed old v ((Effect4.Scope.removeUnsafe_finalizers_sublist entry.scope
   key).subset hv)`. The other two bullets stay as they are.
6. `link_preserves` (:2416, the call at :2465): the registered `interruptFiber` is admitted, since its
   `FinalizerAdmitted` is `True`:
   ```lean
   exact ⟨c0, c1, ⟨c2.c0⟩, scopeStoreOk_addUnsafe c3 hentry m.state.nextName trivial
     (finalizerTyped_of_admitted root _ fin trivial), c4, c5⟩
   ```

Three call sites keep their arguments (reading): `storesOk_world` (:1575), and
`Commands/Observe.lean:1336`, which calls `scopeStoreOk_removeFinalizer c3 scope key`. Two names
need no change:

- `captureTyped_mono` (:1544) does not clash. This seat declares no name like it; its capture
  transport sits inside `finalizerAdmitted_mono` (tested, `grep`).
- `CaptureTyped` moved from `Assembly.lean` to `Admission.lean` under the same name and namespace,
  so D3's references resolve (reading).

**`Typed/Edits.lean`**: `typedState_reachable_of_steps` (:358-362) applies `reachable_of_ledger`
to `load` and to the decisions. Step 3 left that statement as it was; only the bodies of
`LoadsTyped` and `ReachableTyped` grew a premise, on both sides. Unchanged (reading).

**`Typed/World.lean`** (D3's step 0) now defines `ScopeLive w sc` as `w.state.ScopeLive sc`. That
is definitionally the form this seat's base reads, `(w.state.scopes.entryAt sc).isSome = true`.
Two places here read the unfolded form: `scopeAdd_implements`' `replace pre : … := pre.1`, and the
`#guard_msgs` fixture's pinned message. Both see the same terms (reading). `scopeLive_mono` keeps
its signature on main (tested, `git show`).

**The OCaml face.** Main's core changed since the base only under `Effect4.Schema` and
`Effect4.Codegen` (seat W1). No declaration under either appears in the LCNF closure tables
(tested, `cut` and `grep`: 0 rows). So, by reading the tables, main's changes do not move the cut
and this branch's four files stand after the merge. `make gen-lcnf` on the merged tree would test
it.

### With seat D2

`seat/D2` was first read at `5f8cbe18` and re-read at `5e82aacf`, D2's receipt, stopped by the
owner. Its two newer commits add `Membership.lean`'s host-row bridge (row 183) and the receipt,
and the conflict set is unchanged. The dry run (tested):
`git merge-tree --write-tree --name-only --messages seat/D2 c0e608e4` exits 1, with conflicts in
`Typed/Assembly.lean`, `AwaitLoad.lean` and `FitsOrder.lean`. Each needs a hand resolution:

- **`Typed/Assembly.lean`, three regions.**
  - (1) and (2), the capture lemmas. D2 moved `envTyped_append` (and `envTyped_nil`) to
    `Typed/Denotation.lean`, which its `Assembly.lean` imports. D2 also gave `capture_lookup` the
    completed-view premise `hview : ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty
    q.2`, which is row 175's `PointTyped` clause. This seat replaced `capture_lookup`'s body by
    `capture_release` (the release's error column is `never`) and made `capture_lookup` its
    corollary. Resolution: drop `envTyped_append` from `Assembly.lean`. Give `capture_release`
    D2's `hview` premise, and its tuple D2's last component:
    `refine ⟨r, ⟨release, env ++ [a.answer, .exitOf .unknown .unknown], ?_, hrel, ?_, hview⟩, hnever⟩`.
    Give `capture_lookup` D2's statement, proved by
    `(capture_release root w c completed exVal h hex hview).imp fun _ typed => typed.1`.
    D2's ledger declaration `M3bAssembly.capture_lookup` already carries `_hview` (it
    auto-merges), so the `#obligation_proved` line stands with that statement.
  - (3), `loadsTyped_of_denotesTyped`: `intro _ checked closed _` (step 3), then D2's
    `have wf := layerRefsWF_of_typeOf checked` and D2's body.
- **`finalizerTyped_of_admitted`'s `foreign` arm** (no textual conflict). It reads the
  construction post into `capture_release`: write `fun w4 o4 completed hview => ?_` where it now
  says `fun w4 o4 completed _ => ?_`, and pass `hview` as `capture_release`'s last argument.
  Reading: the construction row's post is the view clause (D2's `constructR_typed`,
  `Denotation.lean:722-728`).
- **The two test files.** Step 3's extra binder meets D2's world argument:
  - `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean:291`:
    `fun _ _ closed _ => ⟨_, machineTyped_load _ rootTy 5 5 closed rfl (code_typed _)⟩`.
  - `FitsOrder.lean:505`:
    `fun _ _ closed _ => ⟨_, machineTyped_load src rootTy3 100 100 closed rfl (prog3_typedF _)⟩`.
- **The clash `merge-tree` cannot see.** `Effect4.Program.Typed.fits_context_inv` is declared
  twice:
  - here, in `Typed/Membership.lean`, at `Fits w v (.handle Ty.contextTarget)`;
  - by D2, in `Typed/Denotation.lean:1045`, at `Fits w v Ty.context`.

  These are the same statement (`Ty.context := .handle contextTarget`, `Program/Ty.lean:213`), so
  the merged build fails with a redeclaration. Delete one. Either copy serves both call sites
  through `Ty.context`'s unfolding. Recommended: keep the `Membership.lean` copy, beside
  `fits_option_inv`, where `Fits` inversions live.
- **Nothing else meets.** By reading `git diff bd5462df seat/D2` and `git grep` on `seat/D2`:
  - `seq_typed`'s statement is unchanged (it is re-proved through `seqGuard_typed`).
  - `Seq.lean` still imports only `Residual`, so `Adequacy` importing `Seq` makes no cycle.
  - `Denotation.lean` reads none of `closeScopeR`, `closeScope_installs`, `storePre`'s `scopeAdd`
    arm, or the scope clause.
  - This seat's tests build no `PointTyped` tuple (tested, `grep`).
  - D2's `closeScope_arm` (`Denotation.lean:2115`) already holds the closing exit's fit as a value
    of `exitOf a e` (`hvfit`, :2124), which row N's option (a) would read.

## Owed, with the exact obstacle

1. **The merge edits above**: D3's six lemmas on main; D2's three regions, the foreign arm's view
   argument and the duplicate. Obstacle: those files are seats D2's and D3's, and the brief says
   never to touch them. The coordinator's stop also withdrew the roots build that would test them.
2. **The roots build**, `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`. Obstacle: the
   coordinator's stop ("skip the roots build, the coordinator runs it at the merge"). What was
   built instead (tested):
   - `Effect4` and `Effect4.Laws` after steps 1 and 2, 555 jobs each;
   - `Effect4.Laws` after step 3, 541 jobs;
   - the 38 test modules that import a changed typed module (`seat-D4/scratch/cone2.txt`), 599
     jobs after steps 2 and 3;
   - step 1's 19 scope-close test modules, 427 jobs.
3. **Step 4's checks**: `make check-gen`, `make check-ocaml`, and the `ts` and `readme` groups.
   Obstacle: the coordinator's stop, and the prerequisites named in step 4. `| build` is the full
   build, and `ts/eff/node_modules` is a package download that was not attempted.
4. **The close-scope pre and the closing exit.** This is a finding,
   `closeScope_pre_admits_unfit_exit` (proved). `closeScope_installs` keeps its `exitFits`
   premise, and the close's command proof (open on main, `M6Ledger.step_loop`) cannot discharge
   it from `I`. Obstacle: it needs a ruling (row N below).
5. **U-02's census row and truth fixture**, the other two records U-01 has. Obstacle: both move a
   gated report (the runtime coverage and the truth result), which belong to the census owner and
   the truth lane. Proposed below.
6. **The corpus and truth lanes**: not run, since they are outside step 4's list. By reading, the
   only truth program that calls `Scope.close` is `pScope`, which closes a scope with no
   finalizer, so its `void` answer is unchanged. Assumed: Lean's 400 generated programs
   (`Test/Program/Gen.lean:278` generates `closeScope`) contain none that closes, through
   `Scope.close`, a scope holding exactly one value-answering finalizer and then observes the
   answer. Such a program would now answer `void` against rc.112's value, a `U-02` disagreement
   to sign, not a defect.

## Lines proposed for the coordinator's files

**`docs/core/decisions.md`** (status lines to append):

- **Row 151**: "**Landed 2026-10-01** (seat D4, `receipt-D4.md`; `1ba84f74`, `d1bf339b`, `1819fc16`; the OCaml face re-cut in `c0e608e4`)
  at the site the brief's amendment records: `Scope.close` (`Machine/Stores.lean`
  `storesCloseScope`, `Laws/Program/InterpR.lean` `closeScopeR`) runs a lone finalizer, then
  answers `void` (`Prim.onSuccessConst` of the finalizer's program and `Prim.success Val.unit`;
  the guard over `denoteFin` with the `seqR` continuation answering `unit`); a failure, defect or
  interrupt passes through; related by `voidedFin_means`. The unsafe close stays rc.112's for the
  `scoped` exit (the literal placement measured `seqOne` 19 → 21 counted operations against
  rc.112's host count; at `Scope.close`, `RuntimeRContract`'s host counts hold). Signed `U-02`
  (`docs/UPSTREAM-BACKLOG.md`; rc.112 answers `5` on the pinned source, Effect 3.21.2 voids;
  `seat-D4/`). Finalizers typed at `⟨unknown, never⟩` by two rows of a new source kind `each` at
  the scope state's finalizer fields (`Preds.FinalizerOk := FinalizerTyped`: every later world,
  every closing exit fitting `Exit<unknown, unknown>`, the release's parameter type); `scopeAdd`'s
  pre reads `FinalizerAdmitted` (a capture's `CaptureTyped`, a non-failing `release`, a present
  scope for the closers), bridged by `finalizerTyped_of_admitted` (proved for every finalizer
  name); `closeScope_installs` reads the store's typing (`finalizers_of_typedState`) and the
  closing exit's fit. Flips: `release_registration_refused` (the base's admission history over
  `OldScopeAddPre`), `failing_release_untyped`; positive `close_zero/one/two_typed`,
  `foreign_typed_unknown`, `foreign_close_typed`; `closeLone` answers `unit` on both machines.
  Open: the close-scope pre does not carry the closing exit's fit (`closeScope_pre_admits_unfit_exit`;
  row N below); `check-gen` and `check-ocaml` owed (`dune build` exit 0). `E4-TYPED-CE-016` repaired."
- **Row 117**: "**Closed-row premise landed 2026-10-01** (seat D4, `7690c6d2`): `LoadsTyped`,
  `ReachableTyped` and `M7Fragment` (field `closedRow`) take `rootTy.requires =
  Env.Requirement.empty` after `ClosedEff rootTy` (rc.112 `Effect.ts:17494-17497`); `DecisionKeeps`
  unchanged; `loadsTyped_of_denotesTyped`, `reachable_of_ledger`, `m7_of_capstone` and seven test
  theorems re-proved with one `intro` or argument each; no proof reads it. `ExitHandlesValid`
  (M7's fourth line) keeps `ClosedEff` alone (not on the ruled list). The per-position clause stays
  a later probe; part two stays open; `E4-TYPED-CE-008` stays seeded."
- **Row 140**: "Seat D4 (2026-10-01): `M3bWorld` gains `finalizerTyped_mono` (row 87's transport
  for the bundle's new `FinalizerOk`; the scope reads 0 open, 7 proved); `M3bAdequacy.closeScope_
  installs` restated (the store's typing and the closing exit's fit replace the `lone` premise,
  proved). The close arm of `loop` (seat D3's, when written) reads `closeScope_installs` with
  `finalizers_of_typedState` and the closing exit's fit (row N)."
- **Row N (new, proposed by seat D4): the close-scope pre and the closing exit.** "`fiberPre`'s
  `closeScope` arm reads the scope's presence only, so typed code may close a scope with an exit
  outside `Exit<unknown, unknown>` (a reified `die badName`), which the closed-scope row (row 140,
  `ScopeExitOk`) refuses at every world: the step writes `closed ex` and no later world types the
  store (`ProtocolPosts.CloseScope.closeScope_pre_admits_unfit_exit`, proved). The same fit is
  `closeScope_installs`' one premise beside the store's typing (a lone foreign finalizer's release
  reads its exit at that type). Options: (a) the arm demands `FitsExit w ⟨unknown, unknown, ∅⟩ ex`
  (rc.112 `Scope.close<A, E>(self, exit: Exit<A, E>)`; a checked exit term's value fits its
  `exitOf a e`, below `exitOf unknown unknown`: seat D2's `closeScope_arm` already holds that fit,
  `hvfit`, `Denotation.lean:2124` at `5e82aacf`, by reading; the synthetic closers carry it from `FinalizerTyped`'s premise); (b) the
  closed-scope row reads closing exits at a weaker type (refused: the release reads its exit at
  `Exit<unknown, unknown>`); (c) leave it to the command proofs as `closeScope_installs`' premise
  (they cannot discharge it from `I`). Recommendation: (a). Edits: `Residual.lean` (`fiberPre`
  splits the shared `scopeExit`/`closeScope` arm; `fiberPre_mono`, `fiberPre_rows_append` one line
  each), the controls that build the close's pre (`close_code_typed`, `close_code_typed_live`), the
  finding flips to red, seat D2's `closeScope_arm`, seat D3's close arm."
- **Row 151's record of the runtime census and the truth harness** (U-01's two other records,
  proposed, not done here): a census mechanism row `scope.close-lone-finalizer` (`internal/effect.ts`,
  anchor `    return state.finalizer(exit_)`, offset -1, 8 lines: `:3788-3795`, "Close with one
  finalizer, the inline slot or a one-entry map, returns that finalizer's effect as is, so
  Scope.close answers its value") with a `divergence` line `U-02`
  `Test/Program/ProtocolPosts.lean`, the join row in `Test/Audit/RuntimeCoverage.lean` at
  disposition `divergence`, coverage `diverged`, and the per-kind pin (`scope` +1); and a truth
  corpus program `pScopeCloseLone` (`closeLone` printed) with a signed `U-02` host exception, as
  `pInterruptEscape` carries `U-01`. Both change a gated report (coverage, the truth result), so
  they are the census owner's and the truth lane's.

**`Test/Counterexamples/REGISTER.md`**:

- `E4-TYPED-CE-016`, status: "REPAIRED 2026-10-01 (seat D4, decisions row 151 (a″), `1ba84f74`,
  `d1bf339b`); SEEDED 2026-10-01"; witness cell, append: "since (a″) (seat D4): `lone_release_answer`
  over `eraseControl` (the failure passes the void); `old_release_registration_admitted` (history
  over `OldScopeAddPre`; the old script pinned failing by a `#guard_msgs (error)` fixture), flipped
  by `release_registration_refused`; `failing_release_untyped`; `foreign_typed_unknown` and the
  corollary `foreign_close_typed` beside `foreign_untyped`; `closeLone` (both machines answer
  `unit`; rc.112 answers `5`, `seat-D4/vendor-scope-close.json`)"; repair cell, replace the
  owner's-decision text by: "decisions row 151 (a″): `Scope.close` voids a lone finalizer's value
  (`storesCloseScope`, `closeScopeR`; signed `U-02`); every finalizer a scope holds typed at
  `⟨unknown, never⟩` (`FinalizerTyped`, the `each` rows); `scopeAdd`'s pre reads
  `FinalizerAdmitted` (`finalizerTyped_of_admitted`); `closeScope_installs` from the store's typing
  and the closing exit's fit; `close_zero_typed`, `close_one_typed`, `close_two_typed`".
- New row (the next free `E4-TYPED-CE` id): "| SEEDED 2026-10-01 (seat D4) | A typed close
  leaves the closed scope's exit typed (the close-scope pre admits only exits the closed-scope row
  types) | `Test/Program/ProtocolPosts.lean`: `CloseScope.closeScope_pre_admits_unfit_exit`
  (`closeScope 0 (die badName)` typed at a world holding the open scope 0; `ScopeExitOk` refuses
  `die badName` at every world) | decisions row N (a): `fiberPre`'s `closeScope` arm demands
  `FitsExit w ⟨unknown, unknown, ∅⟩ ex` |".
- `E4-TYPED-CE-008`: unchanged (SEEDED); repair cell, append: "the closed-row premise landed on M5,
  M6c and M7's fragment (seat D4, `7690c6d2`); part two open".

**`docs/core/system-map.md`**: §9's faithfulness row: "signed divergences (`U-01`, `U-02`)"; the
typed-state vocabulary: "`Scope.close` voids a lone finalizer's value (row 151 (a″), `U-02`), and
every finalizer a scope holds is typed at rc.112's finalizer type `⟨unknown, never⟩` (an `each`
source row, `FinalizerTyped`)"; M5, M6c and M7: "for a checked, closed source whose requirement
row is empty (row 117, rc.112's `runPromise`)".

**`docs/STATE.md`**: "Wave 2 seat D4 (2026-10-01): row 151 (a″) landed (the void at `Scope.close`,
signed `U-02`; finalizers typed by a source row; `E4-TYPED-CE-016` repaired); row 117's closed-row
premise landed on M5, M6c and M7's fragment; one finding (the close-scope pre and the closing exit,
row N proposed); the producer chain re-cut (`lcnf`, the OCaml face) and `dune build` passed;
`check-gen` and `check-ocaml` owed."

## Permissions

No permission was refused, and no download was attempted. The one step that would download,
`bun install --frozen-lockfile` behind `check-gen`'s `readme` group, was not run because of the
coordinator's stop.

The two merge dry runs used `git merge-tree`. It writes objects but no ref or worktree; it is not
`git merge`. The main checkout, the other seats' branches (through `git show` and `git grep`) and
the Effect 3 install outside the repository (`/Users/pooks/Dev/effect-jetstream/node_modules/effect`)
were read only.
