# Brief for Codex: foundations slices 3–6

Repo `lean4-effect4` (Lean 4.33.1). Base: `2bcb99ff` on `refactor/phase1-phase3`, which is the
fast-forward of `codex/foundations-slices` (slices 1 and 2 landed and merged 2026-09-21).
Continue on that branch from that commit; nothing is pushed. Plan of record:
`docs/research/2026-09-20-foundations-plan-and-next-two-slices.md` (decisions D1–D11) as
amended in §1 below (D12–D14). Review of record: `docs/core/post-phase-c-synthesis.md`.

Goal in one sentence: **turn the landed interfaces into the typed-state invariant on the
reference machine, one checked layer at a time, statements before proofs, so that M6's
transition ledger is counted over relations that already have their hard cases proved.**

## 0. The once-over of slices 1 and 2

Both landed as briefed, with checks green and evidence retained.

| slice | landed | verdict |
| --- | --- | --- |
| 1 (`3aa1a9f1`) | `Obligation : Prop`; 329 declarations in 40 files as theorems; the seven amendments with `E4-SCHED-CE-004/005` in `Test/Counterexamples/Machine/Semantics/ActionAtRaceAllPremise.lean`; `#obligation_proved` with 32 explicit references; `#obligation_audit` (237 paired, 0 mismatches); `make check` green | as briefed. The per-declaration `set_option linter.unusedSectionVars false in` on the seven is the honest form (an `omit` would drop the premise). Four Pending reorderings handled by adapter terms, correctly |
| 2 (`2bcb99ff`) | `Source.owner`; `SavedOk`/`ResumeOk`/`CaptureOk` whole (kernel print confirms); table 95 → 86 rows, 85 positions, two refusals; `World.Θ` with `addToken` and the open `park_extension`; `Contracts.lean` with `FrameAccepts`/`StackAccepts`/`SavedOk`/`ResumeOk`/`InterruptProvenance`/`CaptureOk` and the changing-middle example; `make check` green | as briefed, plus two good additions the plan adopts: `FrameProtocols` (the three named-hook arrows as parameters) and `ExitFits := CompletionOk` at the effect type's columns |

Unique ledger at base: 309 obligations, 299 proved, 10 open (the five source-site
memberships, the two trace agreements, `observe_replace_trace`, the M4 handshake, and
`park_extension`).

## 1. Amendments to the plan (minor; the rest stands)

- **D12 Certificate-indexed protocol.** Layer 0 gains a ghost certificate chosen at each
  node: `Protocol.Cert : S.Op → Type`, `pre w op cert`, `post w op cert ans`, and
  `Typed.vis (cert) (hpre) (hk : ∀ w' ≥ w, ∀ ans, post w' op cert ans → Typed … (k ans))`.
  `mono`, `bind`, `widen`, `inl`, `inr_inv` all go through unchanged; the unit certificate
  recovers the landed protocol. Checked: `CertProtocolProbe.lean` in
  `docs/research/2026-09-20-foundations-plan-evidence/`, no axioms. This is the Hoare-logic
  logical-variable pattern, and it is how a polymorphic allocation (`deferredMake`,
  `refMake`, `memoBuild`) names the cell type its continuation will read: the certificate
  is the type the checker assigned at the node; `post` says the fresh key is declared at
  that type. No runtime data changes. This settles row 87's allocation-indexing question.
- **D13 Source admission before protocols.** `PointTyped root w point ty` is the checker at
  a path: the node at `point.path` exists and `check nativeSignature env point.path e = .ok ty`
  with `point.env` typed at `env`. `BodyTyped root w : Body → EffTy → Prop` is by the six
  `Body` constructors (`at_`, `fin`, `raceCleanup`, `acquireIn`, `release`, `layerBuild`).
  The fiber protocol's `pre` for `fork`/`forkIn`/`forkScoped`/`scoped`/`mask` refers to
  `BodyTyped`, never to `TypedProg`; S1 later proves `BodyTyped → TypedProg (bodyR …)`. The
  construction is therefore not circular.
- **D14 Reachability on the reference machine.** `RReachable root fuel cfuel m :=
  ∃ tape, m = (replayEval (interpR root) fuel tape (loadR root cfuel)).machine` (the reference
  replay; `Api.load`'s `Guard.Reachable` is the compiled side and meets it through
  `replay_rel` at M7). Typed host answers enter as the tape's `answerAsync` completions with
  an `AnswersOk` premise. No `LegalDecision` beyond that.
- `park_extension` moves into slice 3 (world data is slice 3's file).
- The plan's tooling item 4 (`#obligation_audit`) is done; item 6 (`#answer_gate`) is M3a's.

## 2. Standing constraints

- One Lean compiler per checkout; the worktree is yours. Commit by explicit paths; never
  `README.md`; nothing pushed. `-DwarningAsError=true` is on. Receipts and evidence under
  `docs/research/` are force-added (the directory is gitignored).
- Statements before proofs: every new statement is a theorem obligation with its
  `#proof_wanted` marker in the same commit that declares it, under a `#typed_state_obligations`
  gate with an exact ceiling; markers go only with checked evidence, in the same edit.
- No `first`, `simp_all` or `try` written by hand in landed proofs; a catch-all arm is one
  tactic or one rule. Registration shapes of the Phase C receipt apply (`safe -100 apply` for
  whole-statement rules, `norm simp` for `let`-sided equations, `unsafe 90% apply` for
  single conclusions).
- Build what you touch, `make check` at the end of each slice, `make check-full` not
  required. No generator runs in slices 3–6 (no runtime source changes).
- Stop the slice, record the smallest amendment, and continue other work on: a checked
  counterexample to a frozen statement; a relation that needs runtime data the machine does
  not carry (that would be a runtime tag: refused by rows 44–45); a reachable case a source
  row refuses; an interface that cannot state a hard case in §4/§5.

## 3. Slice 3: world validity and transport (M2 completion; row 87 first half)

**Read.** `Typed/World.lean` (all), `Typed/Contracts.lean` (`ExitFits`, `ResumeOk`),
`Laws/Machine/Handles.lean:860–900` (`Machine.World`, `Handle.existsIn`),
`Machine/Fibers.lean:239–300` (`RunFiber`, `park`, `Parked`), `Program/Typed.lean:34–70`
(`Val.hasTy`, the `allocated` argument), `Machine/Stores.lean` (`Stores.WF`, `HeapNat`,
`refMake`/`deferredMake`/`memoBuild` arms), the review §5.2.

**Files.** `Typed/World.lean` (prove `park_extension`; nothing else moves), new
`Typed/Validity.lean`, controls in `Test/Program/TypedWorldValidity.lean` (new; add to
`Test/All.lean`).

**Statements (all obligations first, gate `Typed.M2Validity`).**
- `WorldValid (w : World) (m : RState) : Prop` with these clauses, each a named field:
  `fibers : ∀ id, (w.Γ id).isSome ↔ id ∈ m.fibers.map (·.id)`;
  `heap : ∀ key, (w.Ρ key).isSome ↔ key.index < m.state.refs.length`;
  `promises : ∀ key, (w.Π key).isSome ↔ key.index < m.state.deferreds.cells.length`;
  `tokens : ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token → (w.Θ f.id token).isSome`;
  `state : w.state = m.state`; `wf : m.state.WF`; `cells : HeapTable w ∧ PromiseTable w`
  (the existing columns); `completions : ∀ key cell, cells[key]? = some cell → ∀ c, cell.completion = some c → CompletionOk w (types of key) c`
  (so an `ofRefGet` names a live typed heap cell); `root : w.Γ Api.root = some rootTy` as a
  parameter of the record.
- Allocation exclusion as corollaries: `valid_refMake_fresh : WorldValid w m → w.Ρ ⟨m.state.refs.length⟩ = none`,
  the same for `deferredMake` and for a fresh token (`nextToken`).
- Transport, each an obligation: `ValueOk`, `CompletionOk`, `HeapTypedAt`, `PromiseTypedAt`,
  `ExitFits` are monotone under `w.le w' ∧ w.state.externals.allocated = w'.state.externals.allocated`.
  State the premise as a named relation `World.leHost w w'`; prove `leHost` is a preorder and
  projects to `World.le`.
- Witnesses: `worldOf (loadR e fuel)` valid at `rootTy`; negatives for a ghost declaration at
  the next heap index, a changed external spelling breaking `ValueOk` transport under bare
  `World.le` (the existing `heapNotMonotone` shape), a wrong nested handle type, a dangling
  `ofRefGet`. Each negative is a theorem of the negation, no `decide` on functions.

**Deletions.** None.

**Build.** `lake build Effect4.Laws.Program.Typed.World Effect4.Laws.Program.Typed.Validity
Test.Program.TypedWorldValidity`, then `make build`, `make check`.

**Finish.** Gate `Typed.M2Validity` at ceiling 0 except any transport lemma that needs M3a's
`TypedProg` (there should be none: every clause here is about data); `park_extension`
closed; the four negatives and the positive witness at `[propext, Quot.sound]`.

## 4. Slice 4 = M3a: protocols, admission and `TypedProg` (row 87 second half; row 86's fill)

**Read.** `Laws/Effects/Protocol.lean` (all), `CertProtocolProbe.lean`,
`Laws/Program/Sched.lean:97–210` (`FiberOp`, `FiberOp.answer`, `FiberSig`, `RSig`),
`Machine/Stores.lean` (`SyncOp`, 31 constructors; `syncOpStep`), `Laws/Program/Progress.lean:340–362`
(`progress`), `Laws/Program/EvaluateR.lean` (`bodyR`, the operation arms 150–260),
`Laws/Program/InterpR.lean:280–320` (`interpR`'s `iterNext`, `loopEnter`, `loopResume`,
`cancelThenFail`), `Program/Checker.lean:96–130` (`check` at a path), `Typed/Contracts.lean`,
the composed graph `2026-09-18-typed-state-composed-graph.md` §4, the review F3 and §5.3.

**Files.** `Laws/Effects/Protocol.lean` (D12 in place: add `Cert`, re-prove the five laws as
in the probe, add `Protocol.plain`); new `Typed/Admission.lean` (`PointTyped`, `BodyTyped`,
the point-environment typing); new `Typed/Residual.lean` (`Ψ_S`, `Ψ_F`, `TypedProg`,
`HandlesFit`, `frameProtocols : Contracts.FrameProtocols`); new `Laws/Auto/AnswerGate.lean`
(`#answer_gate`: every `SyncOp` and `FiberOp` constructor has exactly one pre/post clause;
prints the constructor-to-clause table; a constructor without a clause is an error); controls
in `Test/Audit/AnswerGate.lean` and `Test/Program/TypedResidual.lean`.

**Statements.**
- `Ψ_S : Protocol World StoreSig`. `Cert`: `Ty` for `refMake`, `Ty × Ty` for `deferredMake`
  and `memoBuild`, `PUnit` otherwise. `pre` = `progress`'s hypotheses restated over the world
  (`WF`, `HeapNat`, the request value typed and valid). `post w' op cert ans` = the answer
  typed at the row's answer type and valid in `w'.state`, `w'.state.WF`, and for an allocation
  the fresh key declared at `cert` in `w'` (`w'.Ρ key = some cert`, etc.). Internal operations
  (the non-public `SyncOp` rows) get their own clauses; `progress` is the adapter theorem for
  the public rows, not the definition.
- `Ψ_F : Protocol World FiberSig`, forty arms by family, answers by `FiberOp.answer`:
  `fork`/`forkIn`/`forkScoped` (cert = child's `EffTy`; pre `BodyTyped`; post `ans = Val.fiber id ∧ w'.Γ id = some cert`);
  `await target mode` (pre `(w.Γ target).isSome`; post the exit fits `Γ target`, or the value for `awaitValue`);
  `awaitAll`/`awaitAllFailFast` (post: the collected exits fit their targets); `raceAll`
  (cert = the common type; post the exit fits it); `async` (post: `ExitV` fits the cert);
  `scoped`/`mask`/`closeScope`/`scopeExit`/`guard_`/`unguard`/`finishFinalizer` (exit-carrying: the exit fits the body's cert);
  `gen`/`loop`/`closeIter` (post: the exit fits the cert; the hook protocols supply it);
  `yieldNow`, `interrupt*`, `getId`, `getContext`, `setContext`, `snapshotChildren`,
  `awaitNewChildren`, `runIn`, `dropObservers`, `suspend`, `sync`, `ambientScope`,
  `closeWalk`, `foreignRelease`, `raceRegister`, `cancelRace`, `construction`, `frontier`:
  value or unit answers typed at their obvious type; `refuse`: pre `False` (unreachable under
  typing; the no-`badShape` corollary lives here).
  Rule: a postcondition must be satisfiable by the machine's actual delivery for every arm the
  scheduler answers; the control that catches the opposite is in `Test/Program/TypedResidual.lean`
  (an arm typed only because its post is impossible fails the gate).
- `TypedProg (w : World) (ty : EffTy) (p : RProgram) : Prop :=
  Typed worldOrder (Ψ_S.sum Ψ_F) w (fun w' ex => Contracts.ExitFits w' ty ex) p`.
- `HandlesFit w : Val → Ty → Prop`: a `fiberOf`/`refOf`/`deferredOf` handle's nested type
  agrees with `Γ`/`Ρ`/`Π`; `ValueOk ∧ HandlesFit` is the typed-value judgment M3b assembles.
- `frameProtocols : Contracts.FrameProtocols` from `interpR`'s hooks: `iterator` and `loop`
  arrows by `iterNext`/`loopEnter`/`loopResume` at the named generator or loop; `asyncFinalizer`
  by `cancelThenFail`.
- **The two settling cases, proved in this slice** (they are the reason D12 and D13 exist):
  (i) `refMake` then `refGet` and `deferredMake` then `await`, end to end through `Typed.bind`
  and `inl_inv`/`inr_inv`, at the certificate's type; (ii) an addressed `fork` and a `mask`
  whose body is `BodyTyped`, through `Ψ_F`'s pre and post. If either cannot be stated, stop
  and record why.

**Deletions.** None; the old `Laws/Program/Residual.lean` (tag residual) is unrelated and stays.

**Build.** `lake build Effect4.Laws.Effects.Protocol` (with its existing users), then
`Effect4.Laws.Program.Typed.Admission Effect4.Laws.Program.Typed.Residual Effect4.Laws.Auto.AnswerGate
Test.Audit.AnswerGate Test.Program.TypedResidual`, then `make build`, `make check`.

**Finish.** `#answer_gate` green with the printed table (31 + 40 rows); the two settling
cases at `[propext, Quot.sound]`; the impossible-post control red-then-green; gates
`Typed.M3aWanted` at their declared ceilings with every open name listed in the receipt.

## 5. Slice 5 = M3b/M4: assembly and the first hard proofs

**Read.** slice 4's modules, `Typed/State.lean` (the generated `Preds`, `RStateOk`),
`Typed/Contracts.lean`, `Laws/Machine/Book.lean:226–260` (`PendingOk`, `MachineOk`),
`Laws/Program/EvaluateR.lean:60–150` (`popR`, `pushR`, `saveAnswerR`, `answerR`),
`Machine/Fibers.lean:1834–1850` (the resume arm), `Machine/Fibers.lean:2080–2170`
(`stepDecisionState`, `replayEval`), the composed graph §4 L2–L3.

**Files.** New `Typed/Assembly.lean` (`preds : Preds World`, `TypedState`, `RReachable`,
`AnswersOk`), new `Typed/Stack.lean` (`popR_typed`, `saveAnswerR_typed`, delivery), new
`Laws/Machine/Keeps.lean` (the unary ladder, imports `Machine/Fibers` only), controls in
`Test/Program/TypedStateContract.lean` (new).

**Statements.**
- `preds : Preds World`: `program w e p := TypedProg w (expectTy w e) p` where `expectTy`
  reads `Γ Api.root` for `.root` and `Γ id` for `.fiber id` (D7); `SavedOk := Contracts.SavedOk TypedProg frameProtocols`;
  `ResumeOk := Contracts.ResumeOk TypedProg`; `CaptureOk := Contracts.CaptureOk envAt`;
  `exit := ExitFits`; `HeapCell`/`PromiseCell`/`PromiseTable` from World; `PendingOk`: every
  pending entry's token is in Θ at the fiber and `Book.PendingOk`'s clause; `RaceOk`: entrants
  in Γ, winner/failures fit, the host's saved frame expects the race's type; `ServiceOk`: every
  present service typed *and* the program's requirements present (row 51's second half).
- `TypedState (root) (w : World) (m : RState) : Prop := WorldValid w m ∧ RStateOk preds w m ∧
  (∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token → ∃ tin, w.Θ f.id token = some tin ∧ …
  the saved frame's stack input is tin)`. The last clause is the active-delivery correlation.
- `RReachable` (D14) and `AnswersOk`.
- `typedState_load : ∃ w, TypedState root w (loadR root fuel)` — declared as an obligation with
  a marker in this slice (its proof is M5's initialization); the control is that it *elaborates*.
- **Hard proofs, in this order, each an obligation first:** `popR_typed` (seven slots; the
  intermediate type differs from the final on the `answer` and `resume` arms);
  `saveAnswerR_typed`; `deliver_active` (the resume arm with a matching guard installs code
  typed at the frame's input) and `deliver_stale` (a mismatched token leaves the fiber
  unchanged, which is `ParkHandshake`'s inert disjunct); `capture_lookup` (an addressed
  capture's environment is the checker's at its root/path); then the `Keeps` ladder for the
  transitions those four use.

**Deletions.** None.

**Build.** `lake build Effect4.Laws.Machine.Keeps Effect4.Laws.Program.Typed.Assembly
Effect4.Laws.Program.Typed.Stack Test.Program.TypedStateContract`, then `make build`, `make check`.

**Finish.** The four hard proofs at the trust ceiling; negatives fail for the intended
semantic reason (a wrong middle type; a stale token that would deliver); every refused source
edge either discharged or listed. If the interfaces cannot carry `popR_typed`, stop and amend
slice 4 before any S2 work.

## 6. Slice 6: the residue and the memo, beside slices 3–5

Independent of 3–5; take them when the compiler is idle or a second seat exists.

- **Site membership.** One lemma `mem_supervision_of_at` (from `Node.at_ (.eff program) path =
  some (.eff (.withFiber a))` to the site's membership in `supervision program`, by induction
  on the path through `cata_eff superAlg`), then the five `source_*_site` corollaries.
- **Trace agreement.** `step_agrees` on `Guard.Reachable`: every `emit` of `forked` is inside
  `spawn`, every origin write is in `spawn`; prove per step arm; then `reachable_agrees`; then
  `forkedOf` becomes a control and goes (R79.2).
- **Observation erasure.** `observe_replace_trace`: one projection lemma per reader of
  `Run.observe` (`inspect`, `outstanding`, `pendingReplies`, `retired`, `applied`,
  `fiberStatuses`, `HostProtocol.observe`), then `simp`.
- **Memo (its own commit, runtime).** `MemoIdsOk s := (s.memo.map (·.id)).Nodup ∧ ∀ m ∈ s.memo,
  m.id.index < s.nextName`; `memoIdsOk_empty`; preservation by every `SyncOp` arm; the no-op
  lemma `updateEntry_id_of_ok`; then delete the identity write in `memoComplete`; regenerate
  in the order derived → lcnf → eff → wire → cas with `LEAN_NUM_THREADS=1`; OCaml build and
  the differential run; restate the memo census witnesses. Keep the malformed-store
  counterexamples as the domain boundary.

## 7. After slice 5

M5 (S1 `denoteR_typed` by the weight induction of `Intro.lean:27`, `InterpTyped` for the hook
fields, initialization), then M6 (the transition ledger by family: frames and bookkeeping,
delivery and interruption, store operations, fork/join/race, scopes and finalization,
async/timer/due/batches, the outer driver; F5/F6 only when the first coupled update shows
per-field frames are the bottleneck), then M7 (transfer through `replay_rel` and
`BMeans.exitOf` for every recorded fiber exit; the no-`badShape` and no-halting corollaries
as separate statements). Their briefs are written after slice 5's receipt, against what the
hard proofs taught.

## 8. Receipt shape

One receipt per slice under `docs/research/2026-09-21-foundations-sliceN-receipt.md` with:
base and head; the statements added (names, gates, ceilings before and after); the proofs
landed and their axioms; the controls and their red-then-green logs; commands with exit
codes; what stopped the slice, if anything, with the smallest amendment proposed; the unique
ledger line (`total; proved; open` with every open name). Numbers come from the logs of
that run, never from an earlier receipt.
