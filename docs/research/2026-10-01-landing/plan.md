# Landing plan: every finding of the formal pass, to full completion

Written 2026-10-01 by the coordinator at `dceae006` on `refactor/phase1-phase3` (Codex's G, H1,
H2 part one and row 39 merged at `0c534f06`). The owner's standing instruction (2026-10-01):
resolve all the findings of the verifiers and the synthesis; do not stop implementation until the
most robust, comprehensive, rigorous and clean Lean reification, proof graph and ergonomic basis
are landed, allowing seamless lowering and verified implementations of the core effect, fiber,
store and typing machinery; no shortcuts, no gaps; work until full completion.

This note is the tracker: every finding, its action, its seat and its wave. Seats are Opus
(`opus-max`) agents in their own worktrees (`/Users/pooks/Dev/lean4-effect4-seat-<X>`, branch
`seat/<X>`), each with a brief in this folder and a receipt it writes back; the coordinator
verifies and merges by explicit paths, regenerates the map at each code landing and keeps the
registers. The formal pass is `docs/research/2026-10-01-formal-pass/` (seats `algebra`, `proofs`,
`types`, `organization`, each with a `verify.md`; `rerun-on-0c534f06/README.md` says which probes
still elaborate on the merged tree: the machine-level facts do, the last step of each refutation
must be restated against `CodeInert`, the scheduler facts and `ExitOk`).

## 0. The shape of the answer (what the pass established)

**Fundamental (a milestone statement is false as declared; every repair is a statement change,
no runtime change):**
1. **M5 is false through `Fits`'s raw order** (TY-01, proved twice): the handle arms compare a
   declared type with raw `Ty.sub`, the checker compares and joins in the normalized order
   (`sub (normalize a) (normalize b)`, `join = normalize ∘ union`). Repair: the arms in the
   checker's order, then `fits_normalize`, `fits_subN`, `fits_join_left/right` (proved on a copy,
   `types/verify-AmendedFitsProbe.lean`).
2. **M5 is false through the await-by-value post** (G6, proved on the typed corpus's own
   `awaitFiber.value`): `fiberPost` reads the target's answer column where the checker and the
   machine use the encoded exit. Five more posts contradict their handlers (close-scope,
   `closeIter`, three store rows at `bool` where the store answers `unit`), two pres are too weak
   (`refModify`, `refModifySome`), `memoRelease` and the frontier arm are unaccounted for. Repair:
   the posts at the machine's answers, and one generic adequacy theorem ("the handler answers
   within the protocol's post") instantiated per row, declared in the ledger.
3. **M6's `decision_preserves` and the capstone cannot hold a typed state that types the code of
   running fibers** (G1, proved): a budget cut drops the residue, and the window between a
   fiber's finishing walk and its `finish` is reached by a checked host-free program. Repair: the
   split the lift already supports, keyed on `running`: `J` (machine-only, cut-tolerant) types the
   code of fibers that are neither exited nor running and carries `stuck = none`; `I` adds, for
   each running fiber, typing by the queued command that continues it, plus the queue facts;
   `DecisionLift` unchanged (`proofs/verify-probes/VerifySplit.lean`). This supersedes H1's halt
   extension of row 133 (`CodeInert` on a halted machine): halted machines are outside `J`.
4. **Saved stacks are not Kripke-closed** (ALG-01/G2, proved; `M6Ledger.step_loop` refuted at a
   concrete typed state, `algebra/verify-StepLoop.lean`): `FrameAccepts`'s arms and the hook
   protocols quantify at one world. Repair: the arms and the protocols (`IteratorProtocol`,
   `LoopProtocol`, the async finalizer clause) over later worlds in their definitions; the walk
   restated over Kripke stacks; `savedOk_mono`, `stackAccepts_mono`, `typedProg_mono` (proved)
   in `M3bWorld`; monotonicity of every owner predicate of `preds` declared.
5. **"Never halts" is not a consequence of M6** (G4, proved): the typed state has no clause on
   `stuck`, no scope liveness, no race-id liveness, no typed scope on a queued `link`. Repair: in
   `J`.
6. **Part two of the exit judgment is a coeffect fact** (G5/row 117, proved): presence
   (`Provides ctx ty.requires`) per position, a requires-monotone side condition on
   non-discharging frames, the restored context at `scopeExit`/`release`.
7. **M7 is undeclared and must fix its fragment** (R1; organization M3): empty host table,
   answer-free tapes, observation `obs`, M7a–c; R1's exception for the row table recorded.

**Rigor (a law the plan relies on is absent or owed):** R2 refused source rows (`closed.exit`),
R3 the decision edits and the snapshot as obligations, R4 the two reachability notions and their
`BMeans` bridge, R5 lawful sources on `ProgramSource` (the Σ_app slice: rows 111–116; TY-04, TY-05,
TY-12), TY-03 inhabitance (row 127), TY-07 `evalTerm_fits`, TY-09/TY-10 data stage 1 (rows 119,
128), TY-11 the host receipt bridge (parked with the lane), TY-16 `fiber_inv`, A3/A4 `denoteR_typed`
and the `seqR` bind lemma, A8–A11 the limit, comodel and grading laws, R6 term progress, the
scope-validity invariant (organization M4), the generic protocol adequacy theorem.

**Tidiness:** the lemma landings A5–A7, the census instrument's three blind spots, the five
two-way names, K1–K5's two meanings, the ledger as the one list (M7a–c, monotonicity, edits,
`J`/`I`), controls out of `src/`, the stale docstrings and headers, the registers' drift (STATE,
decisions' order section, coherence, GENERATED, AGENTS), the contract packets that cite deleted
falsifiers, the untracked rulings, the `Effects` import in the core root, the Guard hand
inductions, the twelve slack ceilings, the literature names.

## 1. Owner-level choices (ratified 2026-10-01 for O1 (row 137), O2 (row 138), O4 (row 134) and row 149, "as recommended"; the rest proceed on the recommendation)

| # | Choice | Recommendation, and why |
| --- | --- | --- |
| O1 | TY-01's order: (a) checker's order inside `Fits` and the protocol entries; (b) normalize every checker output; (c) normalize declarations at creation | **(a)**. (b) changes the judgment and the printed faces; (c) leaves raw queries against canonical declarations failing. Re-reads row 96 D1, host-boundary §4.4 ("exactly" = equal normal forms) and `E4-TYPED-CE-006`'s repair text: one line each |
| O2 | M7 against R1 at the row table | **M7 at the empty row table, written into §8 as R1's exception**; DI-57's host-free part (external registration, evaluator selection) is R6's, after M7 |
| O3 | Row 117's contract | **presence clause + requires-monotone side condition** (G5), with scoped and provision positive controls; part two lands after it |
| O4 | Row 133's halt extension (Codex, H1) | **superseded by the `running`-keyed split** (G1): `J` excludes halted machines by `stuck = none`; `StepPreserves`'s dispatch premise stays |
| O5 | `ExitOk`'s two meanings | **rename the meaning-level `Effect4.Program.Denote.ExitOk` to `Denote.ExitHasTy`** (27 declarations, 3 modules, none of the typed state's); land the connector lemma from `FitsExit` under its two premises (proved, `organization/verify-ExitOkConnector.lean`) |
| O6 | The other two-way names | `Effect4.Program.Fits` → `EnvFits`; `Machine.World` → `HandleWorld`; `Ty.Canonical` → `Ty.Normal`; `Api.Typed` kept; wave 3, one seat, after the statement slices |
| O7 | The glossary's home | system map §9 (the map owns the vocabulary), the basis links |
| O8 | `coherence-principle.md`, `traversal-census.md` | keep in `docs/core` with a dated banner; the system map names the census instrument and the census document as the one owner |

## 2. Register ids allocated (SEEDED now, repaired by the seats named; the witness column names the seats' probes at `ea5b28b5`, which no longer elaborate on the merged tree: the tracked ports at `ports-at-dceae006/` are the witnesses the register cites, and `E4-TYPED-CE-011` claims the cut only)

| Id | Claim refuted | Witness | Repaired by |
| --- | --- | --- | --- |
| `E4-TYPED-CE-009` | `Fits` and the checker agree on the order of types (M5 loads every checked program) | `types/M5CounterProbe.lean`, `types/verify-CapstoneProbe.lean` | seat A |
| `E4-TYPED-CE-010` | the await-by-value post describes the delivered value | `proofs/probes/AwaitValuePost.lean`, `proofs/verify-probes/VerifyAwaitLoad.lean` | seat B |
| `E4-TYPED-CE-011` | the saved-code clause types every fiber's code slot on reachable runs and at cuts | `proofs/probes/StaleCode.lean`, `proofs/verify-probes/VerifySplit.lean` | seat C |
| `E4-TYPED-CE-012` | saved stacks transport along world growth (`step_loop` as declared) | `algebra/probes/P2KripkeTyping.lean`, `algebra/verify-StepLoop.lean` | seat B |
| `E4-TYPED-CE-013` | every protocol row is fulfilled by its handler | `proofs/probes/StorePostAdequacy.lean`, `CloseScopePost.lean`, `proofs/verify-probes/VerifyPosts.lean` | seat B |
| `E4-TYPED-CE-014` | the typed state excludes a halted machine | `proofs/probes/HaltTyped.lean` | seat C |
| `E4-TYPED-CE-015` | admission refuses every uninhabited column (DI-67: `prod never nat`, `except never never` admitted) | `docs/research/2026-10-01-data-probe/` (row 127's probe), `types/InhabitedProbe.lean` | seat A |

## 3. Seats and waves

**Wave 1 (parallel, from `dceae006`; E merged `a561d604`, F merged `efcf1ae2`):**
- **E, algebra lemma landings** (`brief-E.md`): A5–A9, A11, the scope-marker laws, the sum
  coproduct, the tape action and `behaviour_unique`, the limit laws, the comodel laws, the
  provision laws and header, the `seqR` bind lemma. Additive; every theorem already proved in a
  probe.
- **F, organization** (`brief-F.md`): the census instrument's blind spots; `Machine/Context.lean`
  out of the `Effects` closure; Guard M1–M3; `foldl_lift` beside the lifts; the `ExitOk` rename
  and connector; the register rows of §2; packets citing deleted falsifiers; GENERATED; the
  untracked rulings force-added; DESIGN-ISSUES' O1–O6.
- **H, DESIGN-BASIS refresh** (`2026-10-01-design-basis-refresh-brief.md` + `brief-H-addendum.md`).

**Wave 1b (after the synthesis is reconciled; parallel):**
- **A, values and the signature**: TY-01 (O1), TY-07, TY-08, TY-02's naming, shape A (row 112),
  the Σ_app definitions (rows 111–116; TY-04, TY-05, TY-12), inhabitance (row 127; TY-03, TY-13,
  TY-14), CE-009 and CE-015 repaired, the first positive M5 control (the TY-01 program loads
  typed). Files: `Laws/Program/Typed/Membership.lean`, `Laws/Program/TypeAlgebra.lean`,
  `Laws/Program/Typed.lean`, `Program/Admission.lean`, `Laws/Program/Typed/World.lean` (serviceTy),
  new `Laws/Program/Signature.lean`; tests.
- **B, frames, posts and the walk**: G6 (posts at the machine's answers; the generic adequacy
  theorem with per-row instances declared), G2/ALG-01 (Kripke closure; the walk; `HookLaws`;
  `saveAnswerR_typed`, `deliver_active`; `typedProg_mono`, `savedOk_mono`, `stackAccepts_mono`),
  TY-16 `fiber_inv`, the frame category laws, `guard_inv`'s docstring, CE-010/012/013 repaired.
  Files: `Laws/Program/Typed/{Contracts,Stack,Residual,Frames}.lean`; tests. Residual's `subN`
  arms (TY-01) after A merges.
- **C, the assembled state, M7 and the lift**: G1 (the `J`/`I` split), G4 (`stuck = none`,
  liveness clauses, scope validity as a declared goal), R1 (M7a–c declared), R2 (`closed.exit`
  un-refused), R3 (the edits and the snapshot declared), R4 (the `BMeans` bridge lemma), T1–T3
  (ledger as the one list; capstone docstring; controls to `Test/`), the running-keyed restatement
  of H1's `CodeInert`, CE-011/014 repaired. Files: `Laws/Program/Typed/{Assembly,Sources,
  Scheduler,TypedStateDecl,State}.lean`, `Laws/Machine/Lift.lean` only if a lemma is missing;
  `M6Capstone.lean`.

**Wave 2 (serial on the merged statements):** row 117's contract and part two, with rows 151 and 152 (the close rows: contract choices whose acceptance is that every existing cleanup and exit-inspection example stays a positive control, one red control per refused shape) and row 153 (M5 for programs with layer references: the redirect-agreement lemma, with a positive control at the corpus's `layer.ref` program) (seat D); the
adequacy instances per row (store rows via `syncOpStep`, fiber rows via the `FiberAction`
helpers, the frontier arm); `Book` once and transported (relative induction); M5's denotation
lemma (`denoteR_typed`, `evalTerm_fits`, `seq_typed`); the easy commands (`evaluate`,
`trackChild`, `exitDone`, `wake`, `drainDue`, `resume`); `finish`/`observe`; the race commands;
`deliver`/`loop` per evaluator arm; the edits; M6c; M7a–c; the reference code-site census as the
list of `I`-typed commands.

**Wave 3:** data stage 1 (row 119; TY-09, TY-10, TY-18; the field-order normaliser; width at
the adapter); the renames (O6); Guard M2 (decision-lift instances); the simple rows 8, 16, 17,
23, 24; the glossary (§9) and the vocabulary edits (ORG-05/06/07/09/10/13/32); R12's carriers
(A10) when R12 opens.

## 4. Rules for every seat

Own worktree and branch from the base the brief names; commits by explicit paths; never
`git add -A`; the research folder force-added; no push; no edit to `docs/core/decisions.md`,
`docs/STATE.md`, `README.md`, `AGENTS.md` or the system map (propose lines in the receipt); one
`lake` at a time in the seat's worktree, `LEAN_NUM_THREADS=4`; narrow builds of touched modules
and their direct dependents, `lake env lean -DwarningAsError=true` for a test; the trust ceiling
`[propext, Quot.sound]`, `#print axioms` for every theorem landed; no `sorry`, `native_decide`,
`partial`, `unsafe`, `axiom`, `extern`, `implemented_by`; no `simp_all`, `first | …`, `try` under
`src/`; hand `simp` as `simp only [...]`; aesop with named banks for proof search in `Laws`; every
new battery reachable from `Test/All.lean` at the anchor the brief names; red controls as
`#guard_msgs (error)` fixtures; plain words; evidence words on every claim. Never touch another
worktree. Read research notes from the main checkout by absolute path; cite `file:line` at the
stated commit. The receipt: the one thing first; base and head; changed files; exact commands and
results; axiom output; open obligations; what is bounded; proposed rows and lines for the
coordinator's files.

## 5. How progress is judged (added 2026-10-01, on Codex's observation)

Laws landing is not the measure. Each seat's receipt reports three things, and the coordinator
reads them before merging:
1. **Which repeated proofs disappeared.** The hand inductions removed (Guard M1–M2), the duplicate
   judgments retired (`Denote.ExitOk`, the one-world walk replaced rather than copied), the per-row
   arguments replaced by one instance of a generic theorem. A landing that adds a lemma nothing
   consumes is recorded as owed consumption, not as progress.
2. **Which program-to-execution connection closed.** The generic handler-adequacy theorem is proved
   (not only declared) by seat B, instantiated at least for the store rows whose posts it fixes,
   and consumed by wave 2's `loop`/`deliver` arms; M5's denotation lemma and the eighteen command
   proofs are the connections that count, and the ledger's open count per scope is the number.
3. **What the eventual claim is.** M7 covers the frame machine at the empty host table on
   answer-free tapes with observation `obs` (row 138, R1's exception); the OCaml engine stays
   outside it until row 28 is ruled; nothing landed here becomes "verified lowering" or general
   host safety, and every receipt says so where it states M7.

The synthesis's corrections to the briefs (§4.5 of `docs/research/2026-10-01-formal-pass/synthesis.md`)
were sent to every seat and recorded on rows 134, 136, 137, 143 and 149 before any merge.

## Amendments (dated)

- 2026-10-01, after seat I's merge (`38686e44`): pass I2 (`brief-I2.md`, seat A on top of seat I)
  carries decisions row 156 as its step 10: scope presence as one predicate (`ScopeLive`), read by
  the five scope-handle posts, the scope arm of `HandleFits`, the `fiberPre` arms and the
  `scopeExit` constructor, with its transport lemma; witnesses `E4-SCHED-CE-020` (seat I's
  `step_deliver_refuted_by_absent_scope`) and `E4-TYPED-CE-018` (Codex's second-eyes review,
  `codex-second-eyes/`: the checked program "make a scope, fork into it" has no `TypedProg`
  derivation). Acceptance: that program and "make a scope, close it" typed as positive controls.
  Wave 2's list is unchanged otherwise; row 154's re-pin follows I2's merge.

- 2026-10-01, the owner: "start the data wave as the probes land". The wave
  (`docs/research/2026-10-01-data-wave/README.md`: the commit series 0–10 with its seats) runs in
  parallel with wave 2; its `Ty` append (commit 4) is sequenced after D1 merges (both touch
  `Membership.lean`); briefs are cut from the probe notes as they land (T and R in; P, Q, S to come);
  W0 (the lean4-typescript bump, row 164) starts first, in the package's own repository.
