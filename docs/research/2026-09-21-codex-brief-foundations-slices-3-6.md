# Brief for Codex: foundations slices 3–6

Repo `lean4-effect4` (Lean 4.33.1). Base: `2bcb99ff` on `refactor/phase1-phase3`, which is the
fast-forward of `codex/foundations-slices` (slices 1 and 2 landed and merged 2026-09-21).
The review below checks the subsequent brief commit `641a0fea`; slices 3–6 have not been
implemented by this review. Implementation uses its assigned branch/worktree and the
coordinator's actual base, including these amendments. Nothing is pushed. Plan of record:
`docs/research/2026-09-20-foundations-plan-and-next-two-slices.md` (decisions D1–D11) as
amended in §1 below (D12–D14). Review of record: `docs/core/post-phase-c-synthesis.md`.

Goal in one sentence: **turn the landed interfaces into the typed-state invariant on the
reference machine, one checked layer at a time, statements before proofs, so that M6's
transition ledger is counted over relations that already have their hard cases proved.**

**Review amendment, 2026-09-21.** Read
[monotonicity and refinement review](2026-09-21-foundations-monotonicity-and-refinement-review.md)
and its [checked controls](2026-09-21-foundations-review-evidence/README.md) with this brief.
The additional theoretical review is input, not a source of new proof claims. The controlling
corrections are incorporated below: actual-transition validity is separate from world
monotonicity; external spelling transport reuses existing proofs; typed leaves and control
markers need stronger contracts; stack preflight precedes M3/M4 closure. Abstract storage
contracts remain target-neutral, with OCaml the first implementation. C compilation, a new
C representation, and a TypeScript target require different, explicitly named connections.

**Implementation preflight, 2026-09-21.** The later adversarial input does not close FR-08.
Kernel-checked controls in `Test/Counterexamples/Machine/Semantics/InterruptDelivery.lean`
refute its entry-mask outcome exception and its claim that deferred interruption replaces a
failing exit. `StrongExitDefect.lean` also refutes its no-badShape consequence for strong cause
typing. See `2026-09-21-foundations-contract-preflight-amendment.md`. The dependent slice 4
residual/control contract is stopped under §2; no production stack judgment is silently changed.
Slice 3 and the independently specified certificate/representation interfaces remain usable.
The full M3a acceptance criteria below are not satisfied by landing those independent parts.

**Approved independent landing, 2026-09-21.** The owner selected D12, C2 and C3/C4 after
slice 3 (`5d63f91d`). These foundations are now implemented and checked; see the
[slice 4 receipt](2026-09-21-foundations-slice4-receipt.md). D12's ledger is a companion
`Laws/Effects/ProtocolObligations.lean`, keeping the generic protocol independent of the
project's proof tooling. C3/C4 land in this independent subset rather than waiting for the
later representation slice. The rest of §4 and the stack contracts in §5 remain held.
The [additional probe disposition](2026-09-21-foundations-independent-probe-disposition.md)
records why the new runtime and WalkPreempted proposals do not close that hold. In particular,
the vendor failure evaluator may discard the continuation returned by getCont; the outer
run loop's earlier interception is a separate comparison boundary. No runtime patch is approved
by this landing, and no unproved scheduler payload is added to the production ledger.

## 0. The once-over of slices 1 and 2

Both landed as briefed, with checks green and evidence retained.

| slice | landed | verdict |
| --- | --- | --- |
| 1 (`3aa1a9f1`) | `Obligation : Prop`; 329 declarations in 40 files as theorems; the seven amendments with `E4-SCHED-CE-004/005` in `Test/Counterexamples/Machine/Semantics/ActionAtRaceAllPremise.lean`; `#obligation_proved` with 32 explicit references; `#obligation_audit` (237 paired, 0 mismatches); `make check` green | as briefed. The per-declaration `set_option linter.unusedSectionVars false in` on the seven is the honest form (an `omit` would drop the premise). Four Pending reorderings handled by adapter terms, correctly |
| 2 (`2bcb99ff`) | `Source.owner`; `SavedOk`/`ResumeOk`/`CaptureOk` whole (kernel print confirms); table 95 → 86 rows, 85 positions, two refusals; `World.Θ` with `addToken` and the open `park_extension`; `Contracts.lean` with `FrameAccepts`/`StackAccepts`/`SavedOk`/`ResumeOk`/`InterruptProvenance`/`CaptureOk` and the changing-middle example; `make check` green | as briefed, plus two good additions the plan adopts: `FrameProtocols` (the three named-hook arrows as parameters) and `ExitFits := CompletionOk` at the effect type's columns |

Unique ledger at base: 309 obligations, 299 proved, 10 open (the five source-site
memberships, the two trace agreements, `observe_replace_trace`, the M4 handshake, and
`park_extension`).

## 1. Amendments to the plan

- **D12 Certificate-indexed protocol.** Layer 0 gains a ghost certificate chosen at each
  node: `Protocol.Cert : S.Op → Type`, `pre w op cert`, `post w op cert ans`, and
  `Typed.vis (cert) (hpre) (hk : ∀ w' ≥ w, ∀ ans, post w' op cert ans → Typed … (k ans))`.
  The generic law patterns survive; `mono` still requires transport for every precondition
  and the result predicate. Preserve/re-prove all existing laws, including `inl_inv` and
  `pure_inv`, and prove the unit-certificate compatibility adapter. Checked: `CertProtocolProbe.lean` in
  `docs/research/2026-09-20-foundations-plan-evidence/`, no axioms. This is the Hoare-logic
  logical-variable pattern, and it is how a polymorphic allocation (`deferredMake`,
  `refMake`, `memoBuild`) names the cell type its continuation will read: the certificate
  is the type admitted at the node; `post` says the fresh key is declared at that exact type.
  Require closed certificate columns where the admitted profile requires them (`Ty.var`
  exists). This addresses allocation indexing; row 87's validity/transport obligations remain.
  Universe zero does not exclude function-valued proof data. No runtime data changes.
- **D13 Source admission before protocols.** `PointTyped root w point ty` is the checker at
  a path: the node at `point.path` exists and `check nativeSignature env point.path e = .ok ty`
  with `point.env` typed at an admitted closed `env`, using existing `FitsWith` and the strong
  value judgment. Explicitly carry `Node.at_ (.eff root) point.path = some (.eff e)` and the
  admitted root identity; `check`'s path argument only locates diagnostics. Include the
  completed-exit view and required context through separate named hypotheses where consumed.
  `BodyTyped root w : Body → EffTy → Prop` is by the six
  `Body` constructors (`at_`, `fin`, `raceCleanup`, `acquireIn`, `release`, `layerBuild`).
  The fiber protocol's `pre` for `fork`/`forkIn`/`forkScoped`/`scoped`/`mask` refers to
  `BodyTyped`, never to `TypedProg`; S1 later proves `BodyTyped → TypedProg (bodyR …)`. The
  construction is therefore not circular.
- **D14 Reachability on the reference machine.** `RReachable root fuel cfuel m :=
  ∃ tape, m = (replayR root fuel tape cfuel).machine`. This wrapper supplies
  `termEvaluatorFor root`. The relation is over driver boundaries, not every internal command
  state. Prove initialization and prefix extension with the command-sufficiency receipt;
  replay stops at a fuel frontier. `Guard.Reachable` is the compiled-side relation and meets
  this through the named `replay_rel` at M7; public journal laws are not that proof.
  `AnswersOk` checks each effective matching `answerAsync` completion at its prefix world,
  target/token and continuation type, with handle validity. A matching answer can resume a
  yield or await, not only an external row. Missing/stale replies are inert in the reference
  controls. Do not add a causal `LegalDecision` restriction without a concrete semantic need.
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
- Build what you touch, `make check` at the end of each implementation slice, `make check-full`
  not required. Slices 3–5 change no runtime source or generated representation. Slice 6's
  separate memo runtime commit does run its listed generators. A review-only probe needs its
  narrow build and checked evidence, not a repeated whole-tree sweep.
- Stop the slice, record the smallest amendment, and continue other work on: a checked
  counterexample to a frozen statement; a relation that needs runtime data the machine does
  not carry (that would be a runtime tag: refused by rows 44–45); a reachable case a source
  row refuses; an interface that cannot state a hard case in §4/§5.

## 2a. Contract preflight before M3a/M4 closure

The retained controls establish gaps in the proposed interfaces. Do this focused contract
work alongside slice 3, before freezing slice 4's concrete residual judgment. Do not postpone
these questions until a large S2 ledger exists.

**Architecture pass first (owner steer, 2026-09-21).** Land module seams, carriers, named
relations, theorem statements and their explicit `#proof_wanted` obligations before filling
the implementation proof bodies. Use the existing `ProofGraph.Obligation : Prop` wrapper
and theorem binders; no `sorry` or axioms. A declared obligation is accounting, not a proof
of its payload. The receipt lists every open name and exact gate ceiling; a checked proof
term is the only event that promotes its status. Keep statements and implementation slices
separate enough to refine the larger model without repeatedly rewriting unrelated proofs.

The research declaration packet in the evidence directory supplies exact reusable statements
for completion transport, indexed storage preservation and representation composition. Its
open obligations are a design prototype outside the production ledger. Promote each to its
named module only after the contract review; the packet does not freeze the unresolved
source/control/delivery judgment by guessing its definition. For these blockers, land the
reviewed declaration and its admission/refusal controls first, then fill its connector proofs.

**Permitted proof-side files for the eventual amendment:** `Typed/Contracts.lean`, the new
`Typed/Admission.lean` and `Typed/Residual.lean`, and their focused `Test/Program/` controls.
Add the counterexample register entry when a frozen production statement is amended. Keep
runtime syntax, evaluators and generated predicates unchanged unless a separate brief
explicitly authorizes them. Record the exact old/new public statement and reason first.

### Resolutions for Preflight Questions & Contract Gaps

1. **Strong values and exits (FR-07 resolved).** Existing `ValueOk`/`ExitFits` are shape/column
   judgments (`Val.hasTy`, `CompletionOk`). They admit forged handles (`ProtocolAdmissionProbe`),
   and `ExitFits` admits `badShapeExit` as an arbitrary defect.
   - *Resolution*: Define `StrongValue (w : World) (ty : Ty) (v : Val) : Prop := ValueOk w ty v ∧ HandlesFit w v ty ∧ HandlesLive w v`.
   - *Live Handles*: `HandlesLive w v` asserts that any `Val.cell key` in $v$ satisfies `key.index < w.state.refs.length`,
     any `Val.deferred key` satisfies `key.index < w.state.deferreds.cells.length`, and any `Val.fiber id` satisfies `(w.Γ id).isSome`.
   - *HandlesFit*: Recursively aligns nested handle types: for `Val.cell key` where `ty = .refOf t`, `w.Ρ key = some t`;
     for `Val.deferred key` where `ty = .deferredOf a e`, `w.Π key = some (a, e)`; for `Val.fiber id` where `ty = .fiberOf t`,
     `w.Γ id = some t`. At `Ty.unknown`, require `HandlesLive w v` without inventing ungrounded phantom parameters.
     For union types `Ty.union t1 t2`, require joint membership in at least one valid branch: `StrongValue w t1 v ∨ StrongValue w t2 v`.
   - *Strong Exits*: `StrongExit (w : World) (ty : EffTy) (ex : ExitV) : Prop := CompletionOk w (ty.answer, ty.error) (.ofExit ex) ∧ (∀ v, ex = .success v → StrongValue w ty.answer v) ∧ (∀ c, ex = .failure c → StrongCause w ty.error c)`.
     `StrongCause` requires every `Reason.fail e` to carry an admitted `valOfErr` satisfying `StrongValue w ty.error v`.
     `badShapeExit` is a Die reason, so this definition still admits it. Error-image admission constrains Fail only. Keep ordinary defects admitted; absence of badShape production requires a separate source/control theorem (checked counterexample `E4-TYPED-CE-003`).

2. **Control forms & marker payload inversion (FR-09 resolved).** In `EvaluateR.lean:90–94`,
   `popR` on `.answer next` consumes a pure exit or `.vis (.inr (.unguard ex')) k` directly and
   discards the marker continuation $k$. Generic protocol typing `Typed o Ψ w Q (.vis (.inr (.unguard ex')) k)`
   only types the discarded continuation $k$, leaving the delivered payload `ex'` unconstrained (`StackProbe.lean:69–96`).
   - *Resolution*: Define a dedicated control-admission predicate `ControlAdmitted (w : World) (ty : EffTy) : RProgram → Prop`:
     $$\text{ControlAdmitted } w\ ty\ (.vis\ (.inr\ (.unguard\ ex))\ k) \iff \text{StrongExit } w\ ty\ ex \land \forall w' \ge w,\ \text{ControlAdmitted } w'\ ty\ (k\ (.success\ .unit))$$
     $$\text{ControlAdmitted } w\ ty\ (.vis\ (.inr\ (.finishFinalizer\ ex))\ k) \iff \text{StrongExit } w\ ty\ ex \land \forall w' \ge w,\ \text{ControlAdmitted } w'\ ty\ (k\ (.success\ .unit))$$
     $$\text{ControlAdmitted } w\ ty\ (.vis\ (.inr\ (.scoped\ point))\ k) \iff \text{PointTyped root } w\ point\ ty \land \dots$$
     For all other operations and pure leaves, `ControlAdmitted` holds by recursion on continuations.
   - *Integrated `TypedProg`*:
     $$\text{TypedProg } w\ ty\ p := \text{Typed } (\text{World.leHost})\ (\Psi_S + \Psi_F)\ w\ (\lambda w'\ ex \Rightarrow \text{StrongExit } w'\ ty\ ex)\ p \land \text{ControlAdmitted } w\ ty\ p$$
   - *Inversion Theorem*: Prove `unguard_payload_inv : TypedProg w ty (.vis (.inr (.unguard ex)) k) → StrongExit w ty ex` by direct projection of the second conjunct, supplying the exact premise needed by `popR.answer`.
   - *Preparation Phase*: `scopeExit` is similarly protected; raw unadmitted dispatch yielding `badShapeExit` (`AnswerShapeProbe`) is excluded.

3. **Failure delivery & error-removing catches (FR-08 reopened by checked preflight).**
   The landed `FrameAccepts.resume.skip` includes every failure and rejects ordinary catches
   that remove Nat errors. Changing skip to guard-miss-only admits those catches, but does not
   prove that actual `popR` preserves the output type. The new input audit's proposed fix is
   false: an initially masked frame with pending interrupt and stack `restoreMask true ::
   resume onFailure :: []` satisfies its entry correlation, then returns the original Nat
   failure at a `never` error column while its exception on the entry mask remains false.
   Moreover `deliverR` only intercepts deferred interruption on success; on failure it clears
   the flag and passes the original failure to `popR`.

   The exact old production judgment remains in `Typed/Contracts.lean`. Do not declare the
   input audit's universal `popR_typed` payload as an accepted obligation. A replacement must
   account for masks and original exits at the actual stack positions visited, preserve
   downstream finalizer input contracts, and cover the admitted source cases. A boolean at
   entry or exit is not that connector. A reachable-state exclusion requires its own checked
   proof and cannot discard the audit's claimed reachable case by assumption. The smallest
   current amendment is to reopen this contract and stop its dependent residual/assembly
   landing; the independent generic certificate and indexed-store contracts do not depend on it.

4. **World transport & spelling extension (FR-01, FR-02 resolved).**
   - *Order Definition*: Define `World.leHost (w w' : World) : Prop := w.le w' ∧ Extends w.state.externals.allocated w'.state.externals.allocated`.
     Prove `leHost_refl : ∀ w, World.leHost w w` and `leHost_trans : ∀ {x y z}, World.leHost x y → World.leHost y z → World.leHost x z`.
   - *Spelling Transport*: Use `extends_append` (`TyView.lean:596–602`) and `hasTy_mono` (`Admits.lean:331–335`).
     Promote Candidate C1 (`completion_transport` in `ArchitectureStatements.lean`) to `Typed/Validity.lean`:
     $$\forall w\ w'\ types\ completion,\ \text{TableExtends } w.\text{Ρ } w'.\text{Ρ} \land \text{Extends } w.\text{allocated } w'.\text{allocated} \land \text{CompletionOk } w\ types\ completion \implies \text{CompletionOk } w'\ types\ completion$$
   - *Separation of Invariants*: Monotonicity under `World.leHost` applies strictly to local propositions (`ValueOk`, `CompletionOk`, `HeapTypedAt`, `PromiseTypedAt`, `ExitFits`, `StrongValue`, `StrongExit`).
     Global `Stores.WF`, `WorldValid`, and coverage are *not* monotone under `World.leHost` (refuted by `WorldReplayProbe.leHost_does_not_imply_wf_transport`);
     they are established as preservation theorems across actual transition steps (`syncOpStep`, `stepDecisionState`).

5. **Placement & Scoped Landing of Architecture Candidates C1–C4.**
   - *C1 (`completion_transport`)*: Lands in `src/Effect4/Laws/Program/Typed/Validity.lean` in Slice 3, proving shape and completion transport under `Extends`.
   - *C2 (`indexed_ref_step_preserves`)*: Proved in `src/Effect4/Laws/Machine/RefKernel.lean` in the independent slice 4 landing. Generalizes `refStepOf_keeps` to heterogeneous heaps indexed by `P : Nat → Val → Prop`: the selected kernel keeps its cell predicate, every other lookup is unchanged, and the answer predicate and heap length are retained. Supplies FR-03's generic heap lemma; concrete M3a protocols still need their row premises.
   - *C3 (`projects_compose`)*: Proved in `src/Effect4/Laws/Machine/Refinement.lean` in the independent landing. Exact step projections compose: if `Concrete` projects to `Middle` with invariant `concreteValid`, and `Middle` projects to `Model` with invariant `middleValid`, then `Concrete` projects to `Model` with invariant $\lambda c \Rightarrow \text{concreteValid } c \land \text{middleValid } (\text{first } c)$.
   - *C4 (`projects_induces_refines`)*: Proved alongside C3. Every valid `Projects` record induces the forward simulation `Refines (fun c m => valid c ∧ project c = m)` on the same answer carrier and Option step. Backend instances and whole-machine connectors remain separate obligations.

**Acceptance:** exact declarations elaborate; caught-error, marker-payload, forged-handle,
open-type, valid-source and pending-interrupt controls distinguish the intended cases;
proof dependencies meet the trust ceiling. Any still-unproved reachable-state exclusion is
an open named obligation and blocks the corresponding M4 closure. Do not weaken a frozen law
or exclude a source-reachable case to make these controls green.

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
- `WorldValid (rootTy : EffTy) (w : World) (m : RState) : Prop` with these clauses, each a named field:
  `ids : w.ids = m.fibers.map (·.id)`;
  `fibers : ∀ id, (w.Γ id).isSome ↔ id ∈ m.fibers.map (·.id)`;
  `heap : ∀ key, (w.Ρ key).isSome ↔ key.index < m.state.refs.length`;
  `promises : ∀ key, (w.Π key).isSome ↔ key.index < m.state.deferreds.cells.length`;
  `tokens : ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token → (w.Θ f.id token).isSome`;
  `tokenBound : ∀ id token ty, w.Θ id token = some ty → token < m.nextToken`;
  token target support in Γ; `state : w.state = m.state`; `wf : m.state.WF`;
  `cells : HeapTable w ∧ PromiseTable w` (the existing columns);
  explicit closedness of admitted Γ/Ρ/Π/Θ columns; `root : w.Γ Api.root = some rootTy`.
  Keep historical Θ entries after delivery; do not identify its domain with active parks.
  Derive stored completion column typing from `PromiseTable`; combine `ofRefGet`'s Ρ lookup
  with exact heap coverage to prove its liveness. Nested payload handles and due/park
  correlation still belong to the stronger invariant in M3/M4, not `Stores.WF` alone.
- Allocation exclusion as corollaries: `valid_refMake_fresh : WorldValid rootTy w m → w.Ρ ⟨m.state.refs.length⟩ = none`,
  the same for `deferredMake` (`w.Π ⟨m.state.deferreds.cells.length⟩ = none`) and for a fresh token
  `valid_nextToken_fresh : WorldValid rootTy w m → ∀ id, w.Θ id m.nextToken = none` (from `tokenBound`).
- `park_extension` proof in `Typed/World.lean`: with `fresh : w.Θ id token = none`, `w.le (w.addToken id token ty)`
  holds because `toWorld`, `Γ`, `Π`, `Ρ` and `state` are strictly identical, preserving `CellCompatible` vacuously,
  and for `Θ`: for target $id$, `tableInsert (w.Θ id) token ty` extends `w.Θ id` by `fresh`; for target $\ne id$,
  `w.Θ target` is unchanged.
- Transport, each an obligation: `ValueOk`, `CompletionOk`, `HeapTypedAt`, `PromiseTypedAt`,
  `ExitFits` are monotone under `World.leHost w w' := w.le w' ∧ Extends w.state.externals.allocated w'.state.externals.allocated`.
  Prove `leHost` is a preorder (`leHost_refl`, `leHost_trans`) and projects to `World.le`.
  Reuse `hasTy_mono` (`Admits.lean:331–335`), `extends_append` (`TyView.lean:596–602`), and `FitsIn.mono`.
  Promote Candidate C1 `completion_transport` (`ArchitectureStatements.lean`) to `Typed/Validity.lean`:
  $$\forall w\ w'\ types\ completion,\ \text{TableExtends } w.\text{Ρ } w'.\text{Ρ} \land \text{Extends } w.\text{allocated } w'.\text{allocated} \land \text{CompletionOk } w\ types\ completion \implies \text{CompletionOk } w'\ types\ completion$$
  Existing keywise heap/promise monotonicity already projects `CellCompatible`; the remaining work is actual-operation compatibility.
  Do not state global `WF`, whole-table coverage or `WorldValid` monotonicity under `leHost` (refuted by `WorldReplayProbe`).
- Witnesses: define the initial ghost-world constructor explicitly; prove its world/machine
  agreement at `loadR e fuel` under admitted closed `rootTy` and the declared source/profile
  assumptions; negatives for a ghost declaration at
  the next heap index; a changed external spelling breaking `ValueOk` under bare `World.le`;
  a fresh dangling cell preserving `leHost` but breaking `WF`; an unconstrained Θ entry at
  `nextToken`; and a dangling `ofRefGet` excluded by valid coverage. Preserve the coarse
  wrong-nested-type false-positive control here; the rejecting strong judgment arrives in
  M3a. Each negative is a theorem of the stated negation, no `decide` on functions.

**Deletions.** None.

**Build.** `lake build Effect4.Laws.Program.Typed.World Effect4.Laws.Program.Typed.Validity
Test.Program.TypedWorldValidity`, then `make build`, `make check`.

**Finish.** Gate `Typed.M2Validity` at ceiling 0 except any transport lemma that needs M3a's
`TypedProg` (there should be none: every clause here is about data); `park_extension`
closed; the named negatives and positive witness at `[propext, Quot.sound]`. Report separately
what is transported under an assumed order and what actual operation establishes that order.
Allocation proofs must cover old cells, fresh cells, table support, spellings and target
validity; the fresh cell alone is insufficient. Prove primitive value/handle transport from
base existence order, table extension and spelling preservation before assembling
`CellCompatible`; do not assume full `World.le` to prove a component of that same order.

## 4. Slice 4 = M3a: protocols, admission and `TypedProg` (row 87 second half; row 86's fill)

Status: the independent D12 and C2 contracts below are proved. The concrete admission,
residual/control protocols, answer inventory and settling program cases remain held.

**Read.** `Laws/Effects/Protocol.lean` (all), `CertProtocolProbe.lean`,
`Laws/Program/Sched.lean:97–210` (`FiberOp`, `FiberOp.answer`, `FiberSig`, `RSig`),
`Machine/Stores.lean` (`SyncOp`, 31 constructors; `syncOpStep`), `Laws/Program/Progress.lean:340–362`
(`progress`), `Laws/Program/EvaluateR.lean` (`bodyR`, the operation arms 150–260),
`Laws/Program/InterpR.lean:280–320` (`interpR`'s `iterNext`, `loopEnter`, `loopResume`,
`cancelThenFail`), `Program/Checker.lean:96–130` (`check` at a path), `Typed/Contracts.lean`,
the composed graph `2026-09-18-typed-state-composed-graph.md` §4, the review F3 and §5.3.

**Files.** `Laws/Effects/Protocol.lean` (D12 in place: add `Cert`, preserve all current law
interfaces through explicit certificate adapters, add `Protocol.plain` and its compatibility
proof); `Typed/Contracts.lean` only for the preflight's recorded amendment;
`Laws/Machine/RefKernel.lean` for the indexed preservation statement/adapter only; new `Typed/Admission.lean` (`PointTyped`, `BodyTyped`,
the point-environment typing); new `Typed/Residual.lean` (`Ψ_S`, `Ψ_F`, `TypedProg`,
`HandlesFit`, `frameProtocols : Contracts.FrameProtocols`); new `Laws/Auto/AnswerGate.lean`
(`#answer_gate`: every `SyncOp` and `FiberOp` constructor has exactly one pre/post clause;
prints the constructor-to-clause table; a constructor without a clause is an error); controls
in `Test/Audit/AnswerGate.lean` and `Test/Program/TypedResidual.lean`.

**Statements.**
- `Ψ_S : Protocol World StoreSig`. `Cert`: `Ty` for `refMake`, `Ty × Ty` for `deferredMake`
  and `memoBuild`, `PUnit` otherwise, requiring `Ty.closed` on certificate columns. `pre` uses
  stable request and declaration demands at `World.leHost`. Global `WorldValid`/`WF`
  and coverage are separate premises of actual-delivery/preservation proofs. Generic cell
  typing uses Ρ/Π, not `HeapNat`; retain `progress` only for its original nat profile.
  `post w' op cert ans` types the actual answer with `StrongValue w' ty ans`, and for an
  allocation declares the fresh key at `cert` in `w'`.
  *C2 integration (`Laws/Machine/RefKernel.lean`)*: use the proved `indexed_ref_step_preserves`
  for non-allocating heap rows, with its exact kernel premise:
  $$\forall (P : \text{Nat} \to \text{Val} \to \text{Prop})\ Q\ op\ cell\ kernel\ before\ after\ ans,$$
  $$op.\text{refKernel} = \text{some } (cell, kernel) \land (\forall i\ v,\ \text{refPeek } before\ \langle i \rangle = \text{some } v \to P\ i\ v) \land \text{RefKernel.Keeps } (P\ cell.index)\ Q\ kernel \land \text{refStep } op\ before = \text{some } (ans, after) \implies$$
  $$Q\ ans \land (\forall i\ v,\ \text{refPeek } after\ \langle i \rangle = \text{some } v \to P\ i\ v) \land after.length = before.length \land (\forall i \ne cell.index,\ \text{refPeek } after\ \langle i \rangle = \text{refPeek } before\ \langle i \rangle)$$
  This discharges non-interference for all unmodified cells without re-proving frame rules per operation.
- `Ψ_F : Protocol World FiberSig`: one manifest row per constructor, with the actual
  dependent `FiberOp.answer` carrier. All 40 arms are classified into four distinct operational categories:

  | Category | Constructors and Carrier | Pre/Post Semantic Contract |
  | :--- | :--- | :--- |
  | **1. Direct Answers** | `getId`, `getContext`, `setContext`, `yieldNow`, `ambientScope`, `sync` (Carrier: `Val`) | `pre`: admitted input values; `post`: returned value is `StrongValue w' ty ans`. |
  | **2. Delayed Delivery** | `await target mode` (`ExitV` for `joinEffect`, `Val` for `awaitValue`), `awaitAll`, `awaitAllFailFast` (`Val`), `raceAll` (`ExitV`), `async` (`ExitV`), `suspend` (`Val`), `interrupt*` (`Val`), `runIn` (`Val`), `awaitNewChildren` (`Val`) | `pre`: target/handle exists in Γ and is valid; `post`: exit or value satisfies `StrongExit`/`StrongValue` for target's type in Γ; matching answers handled by `AnswersOk`. |
  | **3. Control & Preparation** | `guard_` (`Option ExitV`), `unguard` (`ExitV`), `finishFinalizer` (`ExitV`), `scoped` (`ExitV`), `scopeExit` (`ExitV`), `construction` (`List (FiberId × ExitV)`), `closeScope` (`ExitV`), `mask` (`ExitV`), `foreignRelease` (`Val`), `closeWalk` (`Val`), `closeIter` (`ExitV`), `forkScoped` (`ExitV`), `fork`/`forkIn` (`Val`) | `pre`: `BodyTyped` or `PointTyped` with lexical environment concordance; `post`: resulting exit fits body's cert, child fiber registered in Γ, or marker unguards to valid exit. |
  | **4. Live Frontier** | `frontier` (`ExitV`), `refuse` (`Val`) | `pre`: for `refuse`, `False` (unreachable under typing); for `frontier`, live pending state with no completion promised. |

  For every answered row, state an actual-delivery adequacy obligation at an admitted source/state,
  not merely `∃ ans, post ans`. Impossible-post controls in `Test/Program/TypedResidual.lean` enforce satisfiability.
- `TypedProg (w : World) (ty : EffTy) (p : RProgram) : Prop`: defined as the conjunction:
  $$\text{TypedProg } w\ ty\ p := \text{Typed } (\text{World.leHost})\ (\Psi_S + \Psi_F)\ w\ (\lambda w'\ ex \Rightarrow \text{StrongExit } w'\ ty\ ex)\ p \land \text{ControlAdmitted } w\ ty\ p$$
  where `ControlAdmitted` guarantees that top-level control nodes (`.unguard`, `.finishFinalizer`, `.scoped`, `.scopeExit`)
  carry payloads satisfying `StrongExit w ty ex`. This establishes `unguard_payload_inv`, resolving FR-09.
- `HandlesFit w : Val → Ty → Prop`: recursively aligns `fiberOf`/`refOf`/`deferredOf`
  with Γ/Ρ/Π; combined with shape and live-handle validity into `StrongValue`.
- `frameProtocols : Contracts.FrameProtocols` from `interpR`'s hooks: `iterator` and `loop`
  arrows by `iterNext`/`loopEnter`/`loopResume` at the named generator or loop; `asyncFinalizer`
  by `cancelThenFail`. Supply the operational laws required by all `popR` branches:
  failure passthrough where it actually occurs, done/halt results, successor hook and an
  existential new middle type for continuing iterators/loops, cancellation and mask changes.
- **The two settling cases, proved in this slice:**
  1. *Polymorphic Ref Allocation on Heterogeneous Heap*: Prove end-to-end typing for `refMake` followed by `refGet`
     at `Ty.bool` on a heap already containing Nat references (`HeapTypedAt w ⟨0⟩ .nat`).
     Step 1: `Typed.vis` on `refMake (Val.bool true)` chooses `cert = Ty.bool`.
     Step 2: `syncOpStep` produces fresh key $k = \langle \text{length} \rangle$. By `valid_refMake_fresh`, $w.\text{Ρ}(k) = \text{none}$.
     Step 3: use `refMake_extension` and the table insertion laws to prove $w'.\text{Ρ}(k) = \text{some .bool}$ and $\text{HeapTypedAt } w' \langle 0 \rangle \text{.nat}$. C2 does not apply to allocation: `refMake.refKernel = none`.
     Step 4: use C2's no-write row for the continuation's `refGet k`; its actual answer `Val.bool true` must satisfy `StrongValue w' .bool`, closing through `Typed.bind` and `inl_inv` once the concrete protocol is supplied.
  2. *Addressed Fork and Mask with Body Admission*: Prove that an addressed `fork child` with `BodyTyped root w child cert`
     and `mask flag body` with `BodyTyped root w body cert` satisfy `TypedProg`.
     Step 1: `PointTyped` establishes checker agreement at `child.path`.
     Step 2: `Ψ_F.pre` is satisfied by `BodyTyped`.
     Step 3: `post` establishes child fiber $id$ is minted and declared with $w'.\text{Γ}(id) = \text{some cert}$.
     Step 4: Continuation reads child handle as `Val.fiber id` typed at `Ty.fiberOf cert`, closing through `Typed.bind` and `inr_inv`.

**Deletions.** None; the old `Laws/Program/Residual.lean` (tag residual) is unrelated and stays.

**Build.** `lake build Effect4.Laws.Effects.Protocol` (with its existing users), then
`Effect4.Laws.Program.Typed.Admission Effect4.Laws.Program.Typed.Residual Effect4.Laws.Auto.AnswerGate
Test.Audit.AnswerGate Test.Program.TypedResidual`, then `make build`, `make check`.

**Finish.** `#answer_gate` checks a manifest keyed by actual constructor names, rejects
missing/duplicate/stale rows and incorrect dependent carriers, and prints the table (31 + 40
at this base). Kernel-check registered theorem terms against their declared propositions.
Print coverage and semantic proof status separately; inventory coverage is not delivery
adequacy. M3a proves the settling cases and their actual answers, with the impossible-post
control red-then-green. Remaining scheduler adequacy statements are explicit named M6
obligations with declared ceilings; they cannot be counted as proved because the manifest is
complete. Preflight control/stack obligations remain explicit and block their M4 consumers.
Do not build a second catch-all inventory beside `Exhaustive` and the compiled case policy.

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
  reads `Γ Api.root` for `.root` and `Γ id` for `.fiber id` (D7), with declaration existence
  supplied by validity; `SavedOk`/`ResumeOk` are the preflight's amended whole-state/control
  judgments, including its delivery correlation; `CaptureOk` uses the admitted root/path,
  environment and context judgment. Instantiate `exit`, `HeapCell`, `PromiseCell` and the
  due `PromiseTable` with the strong predicates and prove their projections to the existing
  coarse World clauses. In particular retain live/nested handles in stored values,
  completion payloads and exits, and reference-completion liveness. An alternative companion
  invariant must name and retain all those fields explicitly in `TypedState`; the previous
  assignments to `ExitFits` and coarse leaves alone are withdrawn. `PendingOk`: every
  pending entry's token is in Θ at the fiber and `Book.PendingOk`'s clause; `RaceOk`: entrants
  in Γ, winner/failures fit, the host's saved frame expects the race's type; `ServiceOk`: every
  present service typed *and* the program's requirements present (row 51's second half).
- `TypedState (root : NativeEff) (rootTy : EffTy) (w : World) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk preds w m ∧
  (∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token → ∃ tin, w.Θ f.id token = some tin ∧ …
  the saved frame's stack input is tin)`. The last clause is the active-delivery correlation.
- `RReachable (root : NativeEff) (fuel cfuel : Nat) (m : RState) : Prop := ∃ tape, m = (replayR root fuel tape cfuel).machine`.
  `AnswersOk (root : NativeEff) (tape : DecisionTape) (cfuel : Nat) : Prop`: defined inductively along
  the command replay prefix. For each step $i$ consuming an `answerAsync target token payload`,
  requires that fiber `target` is currently parked with `.withGuard token`, and that
  `∃ ty, w_i.Θ target token = some ty ∧ StrongValue w_i ty payload` at prefix world $w_i$.
  Missing or mismatched completions impose no code premise and execute inertly.
- `typedState_load`: under the admitted root/source judgment at explicit `rootTy`, initial
  context/requirements and chosen profile, `∃ w, TypedState root rootTy w (loadR root fuel)`.
  Declare the exact hypotheses with its marker (proof in M5); arbitrary unchecked roots
  are not typed by initialization. The control here is elaboration, not proof closure.
- **Hard proofs, in this order, each an obligation first:**
  1. `popR_typed`: **blocked pending the FR-08 amendment above**. The input audit's
     `DeliveryStateOk` and entry-mask disjunction are refuted by `E4-SCHED-CE-006/007`.
     Keep outcome-indexed typing for active code and completed delivery, with hook laws for
     all seven slots. State the replacement only after the interruption and finalizer
     cases have an admissible model; do not count a false target as mechanical proof work.
  2. `saveAnswerR_typed`: proves that saving the current continuation onto the stack via `saveAnswerR`
     preserves `SavedOk` and intermediate type alignment.
  3. `deliver_active`: for a fiber parked at `.withGuard token` receiving `resume target token code`
     with matching target and token, active delivery installs `current := code`, sets `parked := .notParked`,
     and establishes `TypedProg w tin code` where $tin$ is the declared token type in $\Theta$.
  4. `deliver_stale`: for an arriving resume with mismatched token ($token' \ne token$),
     the transition leaves the parked fiber completely unchanged ($f' = f$), satisfying the inert disjunct
     of `ParkHandshake`.
  5. `capture_lookup`: proves that an addressed capture's lexical environment corresponds to the
     static checker's environment derived from `Node.at_ (.eff root) capture.path`.
  6. `Keeps` ladder: Cartesian lens equations in `Laws/Machine/Keeps.lean` proving that transitions
     modifying store cells or single fibers leave all unrelated fields and validity clauses strictly invariant.

**Deletions.** None.

**Build.** `lake build Effect4.Laws.Machine.Keeps Effect4.Laws.Program.Typed.Assembly
Effect4.Laws.Program.Typed.Stack Test.Program.TypedStateContract`, then `make build`, `make check`.

**Finish.** `popR_typed`, `saveAnswerR_typed`, `deliver_active`, `deliver_stale` and
`capture_lookup` at the trust ceiling, with every hook/control assumption printed. A generic
proof under `HookLaws` does not close the separate concrete interpreter obligation; any
instance awaiting M5 stays open at a declared ceiling. Negatives fail for the intended
semantic reason (a wrong middle type; a stale token that would deliver); every refused source
edge either discharged or listed. If the interfaces cannot carry `popR_typed`, stop and amend
slice 4 before any S2 work. The accepted fragment must still include ordinary error-removing catches
and generated cleanup/guard forms; the retained negatives forbid vacuous closure.

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
as separate statements). No-badShape needs the admitted source/control safety theorem;
no-halting is distinct from termination, fairness and response availability. Their briefs
are written after slice 5's receipt, against what the hard proofs taught.

### Representation and target track

Keep this track distinct from the typed-state slice count. Abstract store contracts, world
transport and representation relations are target-neutral; OCaml is the first implementation
instance. Reuse `Arena`/`LawfulArena`, `RefKernel`, `Projects`/`Refines` and `Factors` at their
exact scopes.

**Architecture Landing in `Laws/Machine/Refinement.lean` (Candidates C3 & C4):**
The independent landing promotes and proves the two obligations from `ArchitectureStatements.lean`:
1. `projects_compose`: proves that exact step projections compose while preserving both concrete
   and middle invariants:
   $$\forall {Concrete\ Middle\ Model\ Op\ Answer}\ (first : Concrete \to Middle)\ (second : Middle \to Model)$$
   $$(stepConcrete : Op \to Concrete \to \text{Option } (Concrete \times Answer))\ \dots$$
   $$\text{Projects } first\ stepConcrete\ stepMiddle\ concreteValid \land \text{Projects } second\ stepMiddle\ stepModel\ middleValid \implies$$
   $$\text{Projects } (second \circ first)\ stepConcrete\ stepModel\ (\lambda c \Rightarrow concreteValid\ c \land middleValid\ (first\ c))$$
2. `projects_induces_refines`: proves that every valid `Projects` instance induces a forward simulation relation:
   $$\forall {Concrete\ Model\ Op\ Answer}\ (project : Concrete \to Model)\ stepConcrete\ stepModel\ valid,$$
   $$\text{Projects } project\ stepConcrete\ stepModel\ valid \implies \text{Refines } (\lambda c\ m \Rightarrow valid\ c \land project\ c = m)\ stepConcrete\ stepModel$$
These compose mathematical projections at the same operation/answer interface once each
instance and its invariant are proved. They do not supply a host-memory or compiler instance.

**The Five-Step Portability Acceptance Criteria for Implementations:**
Each target implementation must supply, in this exact sequence:
1. *Mathematical Model & Observation*: Declare the abstract operations and the observation function (e.g. `Arena.toList`). State whether stepping is deterministic or relational.
2. *Concrete Carrier & Invariant*: State the concrete data structure (e.g., OCaml `e4_table` array, `e4_memo` balanced tree), its well-formedness invariant, and abstraction projection `project : Concrete \to Model`.
3. *Operation Simulation*: For deterministic `Option` steps at the same operation/answer carriers, prove `Projects` or `Refines`, including concrete `none` to model `none` and answer agreement. Effectful, relational or multi-step implementations need a named transition relation with their required stuttering/progress conditions; different keys or values need explicit relations.
4. *World Predicate Transfer*: Transfer the typed-state invariants (`HeapTypedAt`, `PromiseTypedAt`) through the projection; lift the relation through the whole machine.
5. *Target Platform / Host Boundary Profile*:
   - *OCaml 5*: Grounded in `ocaml/engine/e4_table.mli` and `e4_memo.mli`. Must establish density and the selected runtime's integer bounds; the abstract interface proves neither an OCaml implementation nor a fixed word size.
   - *Lean Standard C Compilation*: Follows official Lean runtime code reference; retains Lean runtime reference counting and memory layouts.
   - *Direct C Memory Engine*: Requires an explicit memory/ownership/aliasing model, scalar and allocation-failure semantics, and ABI/FFI obligations.
   - *TypeScript*: The rc.112 image uses the printer/reader connection. A future JS machine target separately specifies its numeric and string domain, containers, mutation/snapshots, execution and host scheduling.

No OCaml container law, compiler rule or bounded integer choice becomes an axiom of
the abstract structure. See review §3 for target differences and proof-transfer acceptance.
Implementing additional backends is not part of slices 3–6.

## 8. Receipt shape

One receipt per slice under `docs/research/2026-09-21-foundations-sliceN-receipt.md` with:
base and head; the statements added (names, gates, ceilings before and after); the proofs
landed and their axioms; the controls and their red-then-green logs; commands with exit
codes; what stopped the slice, if anything, with the smallest amendment proposed; the unique
ledger line (`total; proved; open` with every open name). Numbers come from the logs of
that run, never from an earlier receipt. For every monotonicity or implementation claim,
name its order/relation, source and target, admitted domain, observation, actual theorem or
fresh test, and remaining host boundary. Distinguish a proved conditional interface from a
verified implementation instance. Report every unresolved preflight obligation explicitly.
