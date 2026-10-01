# Seat E receipt: the algebra pass's proved laws, landed beside their objects

Seat E of the 2026-10-01 landing; brief `docs/research/2026-10-01-landing/brief-E.md`, plan
`docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-E`, branch `seat/E`. Written incrementally during the run;
the per-landing log is below the summary.

Evidence words: **proved** (a kernel theorem elaborated here, axioms printed), **tested** (a
finite check run here, a `#guard`), **reading** (code or notes read, not run), **assumed** (not
checked).

## The one thing first

All nine landings are proved at or below `[propext, Quot.sound]` and the final `lake build
Effect4.Laws Test.All` passes (723 jobs; the library-root and axiom gates green), but by plan §5
none of it is progress yet: no repeated proof disappeared, no program-to-execution connection
closed, and the only law with a scheduled consumer is `seq_typed` (M5's `denoteR_typed`, wave 2).
For the merge: three homes differ from the brief because the tree's layering forbids the
brief's (the store-handler laws in a new `Laws/Program/StoreComodel.lean`, since `Laws/Machine`
must not import the `runP` they read; the whole-type provision laws in a new
`Laws/Program/Provision.lean`, since the core root must not import `Ty.join_assoc`; the limit in
a new `Laws/Program/IterLimit.lean` beside `DenoteB`); two names differ to avoid new two-way
names (`Protocol.Le` for P6's `Refines`; no second `Live`); and P5's scope law was not new
(`guardR_bind`, `Laws/Program/Intro/Prepare.lean:44`), so it is cited, not landed again: the
first final build caught the copy, and `a1541c86` removed it.

## Base, head, changed paths

- Base `dceae006` (`refactor/phase1-phase3`); head: the commit that adds this receipt on
  `seat/E` (its parent is `a1541c86`). Eleven commits: one per landing, one fix after the first
  final build, and this receipt: `2bb864c1` (1),
  `8177b65f` (2), `bb2bc76e` (3), `61d2d92a` (4), `d106073e` (5), `3b7ae53a` (6), `35277f40` (7),
  `74db2bd2` (8), `25d2561e` (9), `a1541c86` (6's fix: the duplicate `guardR_bind` dropped),
  and the receipt commit.
- New library modules (6): `src/Effect4/Laws/Effects/Sum.lean`,
  `src/Effect4/Laws/Program/IterLimit.lean`, `src/Effect4/Laws/Program/StoreComodel.lean`,
  `src/Effect4/Laws/Program/ScopeMarkers.lean`, `src/Effect4/Laws/Program/Typed/Seq.lean`,
  `src/Effect4/Laws/Program/Provision.lean`; each imported from `src/Effect4/Laws.lean` at the
  anchor named in its landing.
- Changed library modules (8): `src/Effect4/Laws/Effects/Protocol.lean`,
  `src/Effect4/Laws/Machine/Approximation.lean`, `src/Effect4/Laws/Api/Runner.lean`,
  `src/Effect4/Laws/Machine/RefKernel.lean`, `src/Effect4/Program/Provision.lean` (theorem and
  texts); `src/Effect4/Laws/Program/DenoteR.lean`, `src/Effect4/Laws/Program/Iter.lean`,
  `src/Effect4.lean` (docstring or comment only); plus `src/Effect4/Laws.lean` (six imports).
- New batteries (9), each imported from `Test/All.lean`: `Test/Program/ProtocolLaws.lean`,
  `Test/Program/TypedProgBindRed.lean`, `Test/Program/SignatureSum.lean` (after
  `ProtocolCertificates`); `Test/Machine/Runtime/TapeAction.lean` (after
  `ApproximationContract`); `Test/Api/RunnerFinality.lean` (after `RunnerContract`);
  `Test/Program/IterLimit.lean`, `Test/Program/StoreComodel.lean` (after `DenoteBContract`);
  `Test/Program/ScopeMarkers.lean` (after `DenoteRContract`); `Test/Program/ProvideRows.lean`
  (after `ProvisionContract`). None of these anchors is one another seat's brief names.
- This receipt: `docs/research/2026-10-01-landing/receipt-E.md` (force-added).

## Exact commands and results

- Per landing: `lake env lean -DwarningAsError=true <module>` on every touched module, then
  `LEAN_NUM_THREADS=4 lake build <module> <its direct library dependents>`, then
  `lake env lean -DwarningAsError=true <fixture>`; the exact target lists and job counts are in
  each landing's entry. Every one exited 0. One `lake` at a time throughout; nothing was built
  or run in the main checkout.
- Final: `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`, twice. At `25d2561e` it failed
  only at the root `Effect4.Laws` (the duplicate `guardR_bind`; every other module built,
  6 min 3 s, exit 1; see "Fix after the final build"). At `a1541c86`: **exit 0**, "Build completed
  successfully (723 jobs)", 1 min 31 s, no warning; `Test/All.lean:154` printed "Effect4
  library-root gate: 134 API/utility modules, 218 Laws-only modules; every library source is
  reachable; Effect4 never reaches Laws" (212 Laws-only modules at the base: the six new ones)
  and "Effect4 module and axiom gate: checked 505 modules and 69217 declarations; semantic/test
  axioms are [propext, Quot.sound]; exact implementation boundary (15 module(s), 23
  declaration(s)) additionally allows Classical.choice" (490 modules and 69066 declarations at
  the base; the boundary unchanged). All nine new batteries were built in both runs.
- Axioms: `#print axioms` for every landed declaration, through scratch files importing the
  built modules (`lake env lean -DwarningAsError=true`); the lines are in each landing's entry.
  Nothing reaches `Classical.choice` or `sorryAx`; every landed declaration is at
  `[propext, Quot.sound]` or below. Nine library declarations print no axioms (`Typed.inr`,
  `Typed.inl_iff`, `Typed.inr_iff`, `Typed.refine`, `Protocol.Le`, `restrictL`, `restrictR`,
  `copair`, `storeOp`), and so do nine fixture theorems (`sum_not_tensor`, `budget_not_fixpoint`
  and the seven of `ProtocolLaws.lean`).

## Plan §5: how this landing is judged

1. **Repeated proofs that disappeared: none.** Searched (`grep` over `src/` and `Test/`): no hand
   right lift of protocol typing, no hand restriction of a sum handler, no hand-typed
   `guardR … seqR` sequence, no tape-concatenation induction that `replayEval_append` would
   replace. `Sched.interpret_inl_store` already goes through the package's `interpret_inl` and
   is frozen in `Test/contracts/program-sched.contract.md:102`.
2. **Program-to-execution connections closed: none.** Two landings are components of
   connections: `seq_typed` (with `close_typed`) is the sequencing step of M5's denotation lemma
   `denoteR_typed` (wave 2); `eraseControl_guardR_bind_taken` states the condition under which
   the erased elaboration is the machine's frame-skip sequencing on one fiber, and reading of
   every `guardR` site says `denoteR` meets it (a theorem over the sites is not attempted).
3. **Owed consumption, law by law** (a consumer in `src/` today: none of them).

   | Landed | Consumer owed |
   | --- | --- |
   | `Typed.inr`, `Typed.inl_iff`, `Typed.inr_iff`, `Protocol.Le`, `Typed.refine` | C4 for `TypedProg` (its own inductive; the generic laws do not apply to it) |
   | `sum_is_coproduct`, `interpret_inl_restrict`/`inr`, `inl`/`inr_isMonadMorphism` | DB-01's sum-of-free-theories wording (seat H); any future handler of `RSig` |
   | `replayEval_append` and corollaries | DB-03's divergence by compatible prefixes; R12's run of a decision stream (A10) |
   | `behaviour_unique` | completes the runner's "final Mealy machine" docstring; no theorem user |
   | `Conv`, `conv_fixpoint`, `conv_least`, `conv_unique` | DB-04's wording; R10's first declared loop rewrite |
   | `put_get`, `get_get`, `put_put` | R10's first declared state equation |
   | `eraseControl_guardR_bind`, `eraseControl_guardR_bind_taken`, the `PassesSkipped` instances | M5's elaboration lemma for the scoped forms; the docstring of `denoteR_straight` |
   | `close_typed`, `seq_typed` | M5's `denoteR_typed` (wave 2): the one scheduled consumer |
   | `provideMerge_assoc_rows`, `provideMerge_assoc`, `provide_provide` | a printer step or form that regroups `provideMerge` chains |

4. **The eventual claim.** Nothing here is "verified lowering" or host safety. The laws are about
   the generic protocol logic, the free monad's signature sum, the decision tape on the frame
   machine (any evaluator, finite tapes), the session runner, the budgeted meaning over the store
   signature, the store handler, the scope markers' erasure, one sequencing shape of `TypedProg`,
   and the provision algebra on layer types. M7 (row 138) is not touched.

## Open obligations and what is bounded

- **Owed, created or confirmed here:** C4 for `TypedProg`; the compatibility lemmas for the
  other scoped shapes `denoteR` builds (`onFailure`: `catchCause`, `catchIf`, `orDie`; `all`:
  `exit`, `matchCause`; `onExit`), which M5 needs beside `seq_typed`; a theorem that every
  `guardR` continuation of `denoteR` passes its skipped exits through (reading today);
  naturality, dinaturality and the codiagonal at the limit (only with a declared loop rewrite);
  get-put and distinct-cell commutation at the handler (only with a declared state equation);
  `build_total`'s restoration (R5, now said in both texts).
- **Bounded evidence:** two items are tested, not proved: that `pBindSync` at machine fuel 2 is a
  fuel frontier whose machine is neither stuck nor finished, and the four `#guard`s of the tape
  action's arms on that program (`TapeAction.lean`); the general refutation beside them is
  proved. One item is reading: `denoteR`'s `guardR` sites all use a pass-through continuation.
  No host-only evidence.
- **Not landed, with reasons:** the pedigree's `typed_along` (with `SigMorph`, `along`) and
  `c4_iff` (with `Protocol.pull`): `Typed.refine` is the cleaner shape on one signature,
  `typed_along`'s instances on the tree's signatures are exactly `Typed.refine`, `Typed.inl` and
  `Typed.inr`, and by plan §5 a further unconsumed generic law is owed consumption, not
  progress. The coordinator's message asked to prefer the pedigree's shapes where cleaner; the
  injections' iff shape was taken, the order's was not. Two names were not landed as written:
  P6's `Refines` (a sixth two-way name; landed as `Protocol.Le`) and P4's `Live` (a second
  `Live`; the premise is stated as `c.index < s.refs.length`). P5's `guardR_bind` is not landed
  either: it was already in the tree.

## Proposed lines for the coordinator's files

- **`Test/Counterexamples/REGISTER.md`, `E4-DEN-CE-002`**, the one-line rewording in comodel
  terms the brief asks for (claim column): "The store handler satisfies put-get on every cell:
  on a never-allocated cell the fallback answers `Val.unit` whatever was written
  (`put_get_dead_fails`, `Test/Program/StoreComodel.lean`), so the handler is a lawful comodel of
  state on its allocated cells only (`put_get`, `get_get`, `put_put`,
  `Laws/Program/StoreComodel.lean`)". The repair column ("the `none` arm is the machine's
  fallback, never a defect") stands.
- **`docs/core/decisions.md`** (the algebra note's proposed row 2, the part this seat landed):
  "M5's sequencing tool is per construct, not a bind rule (`TypedProg` is not bind-closed:
  `typedProg_not_bind_closed`, `bind_not_typed`): `seq_typed` (landed,
  `Laws/Program/Typed/Seq.lean`) for `denoteR`'s `bind`; the `onFailure`, `all` and `onExit`
  shapes owed beside it under M5's ledger, with `denoteR_typed` and `evalTerm_fits` (row 148)."
- **`src/Effect4/Laws/Program/Typed/ProtocolObligations.lean`** (D12's ledger; not in this
  brief): its header says it is the ledger "for the laws of `Laws/Effects/Protocol.lean`"; either
  register `Typed.inr`, `Typed.inl_iff`, `Typed.inr_iff` and `Typed.refine` there (four
  `#obligation_proved` lines, all proved) or reword the header to "D12's laws".
- **`tools/Tools/ArchitectureRoles.lean:79`** (the role register, `Laws/Effects`): "layer 0 of
  the typed-state invariant: the protocol-typed predicate on the free monad, and the signature
  sum as the coproduct of the free monads; imports the pinned `Effects` only".
- **`docs/core/coherence-principle.md` §2, row 27**: add `behaviour_unique` to the ✔ list; row 38
  stays ✘ (it asks for finality of run observations, which `behaviour_unique` does not give).
- **DESIGN-BASIS (seat H's refresh)**: DB-01, "the tree's sums are sums of free theories, hence
  conservative (`sum_is_coproduct`, `Typed.inl_iff`/`inr_iff`); a sum of theories with equations
  is Hyland, Plotkin and Power's question"; DB-03, "compatible finite prefixes are the chain
  `replayEval_append` gives, a fuel frontier absorbing"; DB-04, "the budgeted meaning is the
  Kleene chain of the least fixed point; Elgot's laws hold for the limit (`conv_fixpoint`,
  `conv_least`, `conv_unique`), never for one budget (`budget_not_fixpoint`)".

## Log: one entry per landing, written as each commit landed

### Landing 1: the generic protocol layer (commit `2bb864c1`)

- **Shape chosen.** Read before writing: P6 (`algebra/probes/P6ProtocolLaws.lean`) and the
  pedigree seat's `Conservativity.lean` (`inl_iff`, `inr_iff`, `typed_along`) with its verifier's
  `c4_iff` (`VerifyConservativity.lean`). P6's `Typed.inr` and the pedigree's `inr_lift` are the
  same proof. The pedigree's iff shape is stronger and as short (the reflection is one induction
  through the tree's own inversions), so the injections land as the pedigree has them: lift and
  iff. For the order, P6's shape is the cleaner one on a single signature: `typed_along` is the
  same induction along a signature morphism, but it needs a new `SigMorph` structure and a new
  program map `along` (a recursion over `Program`), and its instances on the tree's signatures
  are exactly `Typed.refine` (identity) and `Typed.inl`/`Typed.inr` (the injections). Not landed:
  `typed_along`, `along`, `c4_iff` and the world projection `pull` (no consumer on M5–M7; the
  owed C4 is for `TypedProg`, ALG-05's verdict).
- **Name.** P6's structure `Refines` landed as `Protocol.Le`: `Refines` is already
  `Effect4.Machine.Refinement.Refines` (a forward simulation), and a second declaration with that
  last component would be a sixth two-way name (organization note §5's criterion).
- **Theorems** (`src/Effect4/Laws/Effects/Protocol.lean`, lines at the head): `Typed.inr` `:119`,
  `Typed.inl_iff` `:159`, `Typed.inr_iff` `:170`, `Protocol.Le` `:186`, `Typed.refine` `:194`.
  **Proved**; each prints "does not depend on any axioms".
- **Fixtures.** `Test/Program/ProtocolLaws.lean` (imported from `Test/All.lean` after
  `ProtocolCertificates`): `right_lift`, `left_reflects`, `right_reflects`,
  `exchanged_certificate_refused_in_sum`, `refined` (positive), `promise_needed` (the pedigree's
  `post_refinement_needed`), `demand_needed` (its verifier's `pre_refinement_needed`), and a
  `#guard_msgs (error)` fixture pinning that the identity certificate map cannot place a protocol
  with a weaker promise above `leftProtocol` (`:111`). All seven theorems print no axioms.
  `Test/Program/TypedProgBindRed.lean` (imported after it): `typedProg_not_bind_closed` (P6's
  red control, restated against H2's `ExitOk`: the continuation premise reads `ExitOk w' mid ex`
  and the marker's payload is `ExitOk`; **proved**, `[propext, Quot.sound]`; `:32` at the head),
  and a `#guard_msgs (error)` fixture pinning the constructor's refusal of `nat 0` at `unit`
  (`:64` at the head).
- **Not registered in the D12 ledger.** `ProtocolObligations.lean` says it is the ledger "for the
  laws of `Laws/Effects/Protocol.lean`"; the four new laws are not D12's obligations and that
  file is not in this brief. Proposed for the coordinator: either register them there (four
  `#obligation_proved` lines, all proved) or reword that header to "D12's laws".
- **Commands.** `lake env lean -DwarningAsError=true src/Effect4/Laws/Effects/Protocol.lean` (no
  output); `lake build Effect4.Laws.Effects.Protocol Effect4.Laws.Machine.Lift
  Effect4.Laws.Program.Typed.ProtocolObligations Effect4.Laws.Program.Typed.Residual
  Effect4.Laws.Program.Typed.World` (364 jobs, success; ledger lines unchanged: M3a 0 open, M3bWorld
  1 open); `lake env lean -DwarningAsError=true` on both fixtures (exit 0, only the axiom lines).

### Landing 2: the signature sum is the coproduct (commit `8177b65f`)

- **Theorems** (new `src/Effect4/Laws/Effects/Sum.lean`, imported from `src/Effect4/Laws.lean`
  right after `Effect4.Laws.Effects.Protocol`; it imports `Effects.Algebra.Universal` only), from
  `algebra/probes/P1Coproduct.lean`: `restrictL` `:45`, `restrictR` `:49` (no axioms),
  `eq_sum_restrict` `:53` (`[Quot.sound]`), `interpret_inl_restrict` `:61`,
  `interpret_inr_restrict` `:68` (`[propext, Quot.sound]`), `inl_isMonadMorphism` `:79`,
  `inr_isMonadMorphism` `:85` (`[Quot.sound]`), `copair` `:94` (no axioms), `sum_is_coproduct`
  `:103` (`[propext, Quot.sound]`). **Proved.** The restriction law kept P1's form, which uses no
  monad law (the pedigree's `interpret_along` needs `LawfulMonad`; verifier ALG-06).
- **Fixtures** (`Test/Program/SignatureSum.lean`, imported from `Test/All.lean` in the same
  block): `copair_injections` (`:29`, positive: the copairing of the injections is the identity,
  from the uniqueness half; `[propext, Quot.sound]`), `rHandler_restrict` (`:53`, positive: the
  generic restriction law gives back `interpret_inl_store` at `RSig`; `[propext, Quot.sound]`),
  `sum_not_tensor` (`:39`, the red control; no axioms) and its `RSig` instance
  `store_fiber_do_not_commute` (`:66`, `[propext]`), and a `#guard_msgs (error)` fixture (`:80`)
  pinning that the commutation equation is refused by computation (`rfl`).
- **Not done here.** DB-01's caveat in these terms ("the tree's sums are free, hence
  conservative; a sum of theories with equations is HPP's question") is DESIGN-BASIS text (seat
  H's refresh); the module docstring says it.
- **Commands.** `lake env lean -DwarningAsError=true src/Effect4/Laws/Effects/Sum.lean` (no
  output); `lake build Effect4.Laws.Effects.Sum` (10 jobs, success); the fixture by
  `lake env lean -DwarningAsError=true` (exit 0, axiom lines only). The only direct dependent is
  the root `Effect4.Laws`, built once at the end.

### Landing 3: the tape acts on machines; `behaviour` is unique (commit `bb2bc76e`)

- **Theorems**, from `algebra/probes/P3TapeAction.lean`. In
  `src/Effect4/Laws/Machine/Approximation.lean` (new section "The tape acts on machines", and a
  header bullet): `ReplayResult.thenReplay` `:887` (P3's `thenReplay`, namespaced beside
  `ReplayResult.machine`), `replayEval_of_stuck` `:896`, `replayEval_append` `:904`,
  `replayEval_append_fuel` `:933`, `replayEval_append_machine` `:941`. In
  `src/Effect4/Laws/Api/Runner.lean`: `behaviour_unique` `:187`, with the header and the
  algebra section's item 3 citing it. **Proved**; all six print `[propext, Quot.sound]`.
- **ALG-19.** `behaviour_unique`'s docstring says it is the session runner's law (row 27 of
  the coherence census in `docs/core/coherence-principle.md`), that run observations still have
  no finality law (that census's row 38) and this theorem does not supply one, and that
  decisions row 38 (`explain` onto the fold) is unrelated. So A12's amendment (point the
  coherence document's "(row 38)" at `behaviour_unique`) stays refuted; nothing to change there.
- **Fixtures.** `Test/Machine/Runtime/TapeAction.lean` (imported after
  `ApproximationContract`): `naive_append_fails` (`:35`, red control, for every evaluator: at a
  fuel frontier whose machine is neither stuck nor finished, the naive law "replay the suffix
  from the reached machine" gives a tape frontier where the true replay gives the fuel frontier;
  **proved**, `[propext, Quot.sound]`); the frontier it needs exists (`pBindSync` at machine fuel
  2, **tested** by `#guard`); the law's arms on that program (**tested**, four `#guard`s); and
  the naive law's refusal at that frontier pinned under `#guard_msgs (error)` (`:85`).
  `Test/Api/RunnerFinality.lean` (imported after `RunnerContract`): `replayPlay_phases` (`:23`,
  positive: a journal's play writes `behaviour`), `behaviour_needs_cons` (`:29`, red: the map
  that observes nothing satisfies `behaviour_nil` and differs on every one-row journal), and the
  uniqueness law's refusal of that map at its second equation pinned (`:45`). Both theorems
  print `[propext, Quot.sound]`.
- **Commands.** `lake env lean -DwarningAsError=true` on both modules (Approximation: only the
  `M1OriginApproximation` ledger line, 0 open; Runner: no output); `lake build
  Effect4.Laws.Machine.Approximation Effect4.Laws.Api.Runner Effect4.Laws.Api.Fuel
  Effect4.Laws.Machine.Behaviour Effect4.Laws.Machine.Handles Effect4.Laws.Machine.Lift
  Effect4.Laws.Machine.Scheduling Effect4.Laws.Program.Agreement.Machine
  Effect4.Laws.Api.RunnerBytes Effect4.Laws.Run` (337 jobs, success, 2 min 21 s); both fixtures
  by `lake env lean -DwarningAsError=true` (exit 0, axiom lines only). The test dependents of the
  two modules (`ApproximationContract`, `CompletionContract`, `SchedulerCoreContract`,
  `M6Capstone`, `RuntimeRReference`, `RunnerContract`) are rebuilt by the final `Test.All` build;
  no name they use was added (grep).

### Landing 4: the limit of the budgeted meaning (commit `61d2d92a`)

- **Home.** A new `src/Effect4/Laws/Program/IterLimit.lean` (imported from `Laws.lean` right
  after `DenoteB`), not `Iter.lean`: `Conv` runs a program through `runP`, which is
  `DenoteB.lean`'s, and `Iter.lean` is generic over the signature and runs nothing (verifier
  ALG-08's "beside `DenoteB.lean`"). Its only dependent is the root.
- **Theorems**, from `algebra/probes/P4ComodelIteration.lean`: `Conv` `:42` (`[propext]`),
  `conv_fixpoint` `:48`, `conv_least` `:79`, `iter_finished_succ` `:103`, `conv_unique` `:122`
  (each `[propext, Quot.sound]`). **Proved.** The module header carries the brief's text:
  the budgeted meaning is the Kleene chain of the least fixed point; Elgot's laws hold for the
  limit, never for one budget; naturality, dinaturality and the codiagonal are owed only when a
  loop rewrite is declared (R10).
- **Fixtures** (`Test/Program/IterLimit.lean`, imported after `DenoteBContract`):
  `twoRounds_converges` (`:25`, positive, read off the fixpoint law), `spin_never_converges`
  (`:31`, positive, read off leastness with the empty relation), `budget_not_fixpoint` (`:39`,
  the red control; no axioms), and the budget-1 fixpoint equation's refusal by computation
  pinned under `#guard_msgs (error)` (`:57`).
- **Commands.** `lake env lean -DwarningAsError=true src/Effect4/Laws/Program/IterLimit.lean`
  (no output); `lake build Effect4.Laws.Program.IterLimit` (54 jobs, success); the fixture by
  `lake env lean -DwarningAsError=true` (exit 0, axiom lines only).

### Landing 5: the store comodel's state laws (commit `d106073e`)

- **Home, split by layer.** `refStep_eq_refStepOf` and `syncOpStep_eq_refStepOf` live in
  `src/Effect4/Laws/Machine/RefKernel.lean`, so the machine facts went there. The handler-level
  laws are stated through `runP` (`Laws/Program/DenoteB.lean`), and `Laws/Machine` (layer 2 in
  the role register, `tools/Tools/ArchitectureRoles.lean`) must not import `Laws/Program`
  (layer 3); so they went to a new `src/Effect4/Laws/Program/StoreComodel.lean` (imported from
  `Laws.lean` after `IterLimit`), not `StoresLaws.lean`.
- **Names.** P4's `Live s c` is not landed: `Effect4.Program.Typed.Live` already names value
  liveness at a world, and a second `Live` would be a new two-way name. The premise is stated as
  `c.index < s.refs.length` ("allocated": the heap only grows). P4's `op` landed as `storeOp`,
  `runP_op` as `runP_storeOp`, its three helpers as `syncOpStep_refSet_allocated`,
  `syncOpStep_refGet_allocated`, `syncOpStep_ref_unallocated`.
- **Theorems.** `RefKernel.lean`: `syncOpStep_refSet_allocated` `:113`,
  `syncOpStep_refGet_allocated` `:121`, `syncOpStep_ref_unallocated` `:129` (each
  `[propext]`). `StoreComodel.lean`: `storeOp` `:39` (no axioms), `runP_storeOp` `:42`,
  `put_get` `:51`, `get_get` `:67`, `put_put` `:88` (each `[propext, Quot.sound]`). **Proved.**
- **Fixtures** (`Test/Program/StoreComodel.lean`, imported after `Test.Program.IterLimit`):
  `put_get_one_cell` (`:20`), `put_put_one_cell` (`:25`) (positive, premise by `decide`),
  `put_get_dead_fails` (`:33`, the red control, P4's name kept), and `put_get`'s refusal of the
  never-allocated cell pinned under `#guard_msgs (error)` (`:53`: `decide` proves the premise
  `{ index := 0 }.index < List.length Stores.empty.refs` false). All three theorems print
  `[propext, Quot.sound]`.
- **Commands.** `lake env lean -DwarningAsError=true` on `RefKernel.lean` (ledger lines only:
  `RefKernelObligations` 0 open, `ArenaObligations` 0 open, `M1.RefKernelSupport` 0 open) and on
  `StoreComodel.lean` (no output); `lake build Effect4.Laws.Machine.RefKernel
  Effect4.Laws.Machine.Refinement Effect4.Laws.Machine.StoresLaws Effect4.Laws.Program.Progress
  Effect4.Laws.Program.StoreComodel` (256 jobs, success); the fixture by `lake env lean
  -DwarningAsError=true` (exit 0, axiom lines only).

### Landing 6: the scope markers (commit `3b7ae53a`, fixed by `a1541c86`)

- **Home.** A new `src/Effect4/Laws/Program/ScopeMarkers.lean` (imported from `Laws.lean` after
  `EvaluateR`; after the fix it imports `Intro.Prepare`, which brings `EvaluateR`'s
  `GuardKind.hasExitArm` and the existing `guardR_bind`), so `DenoteR.lean`'s many dependents
  only see a docstring change.
- **Theorems**, from `algebra/probes/P5ScopeMarkers.lean`: `eraseControl_guardR_bind` `:47` (the
  erasure law, `[propext, Quot.sound]`). **P5's scope law `guardR_bind` was not new:** the tree
  has it at `Laws/Program/Intro/Prepare.lean:44` (same statement, the normal branch's tail
  named `unguardTail`); neither the algebra seat nor its verifier cited it. My first commit of
  this landing restated it in `ScopeMarkers.lean`, which elaborated alone and failed the final
  build's root import ("environment already contains `Effect4.Program.Sched.guardR_bind.match_1`
  from `Effect4.Laws.Program.Intro.Prepare`"); the fix commit (see "Fix after the final build")
  drops the copy, imports `Intro.Prepare`, and the docstring and the red control cite the
  existing theorem. A name scan of every other declaration landed here found no second
  duplicate.
- **ALG-12's nuance: stated and proved, a few lines.** `PassesSkipped kind k` `:54` (on every exit
  the guard's arm does not take, `k` answers that exit unchanged; `[propext]`) and
  `eraseControl_guardR_bind_taken` `:61` (`[propext, Quot.sound]`): for such a `k`, the erased
  scope is the erased body followed by `k` on the taken exits and by nothing on the others, the
  frame skip of `popR` on one fiber. Instances for every continuation shape `denoteR` uses:
  `seqR_passesSkipped` `:76` (after `onSuccess`), `passesSkipped_onFailure` `:84` (the
  success-passing match after `onFailure`: `catchCause`, `catchIf`, `orDie`, the finalizer's
  cleanup), `passesSkipped_all` `:94`, `passesSkipped_onExit` `:99` (those guards skip nothing);
  each `[propext]`. **Reading, not proved:** that every `guardR` site of `DenoteR.lean` uses one
  of these shapes. The source has sixty `guardR` occurrences (47 `onSuccess`, 8 `onFailure`, 4
  `all`, 1 `onExit`, counting the unfolding equations that restate the arms); a script over the
  text confirmed each `onSuccess` guard's continuation is `seqR` (one false alarm at
  `finalizerR`, `:77`, whose inner `onFailure` bind comes first; its outer bind is `seqR`) and
  each `onFailure` guard's is the success-passing match. One sentence
  added to `denoteR_straight`'s docstring (`DenoteR.lean:1378-1384`) says the reading of the
  erased elaboration as the one-fiber meaning rests on this, and that the site claim is a
  reading. So nothing of ALG-12 is left owed except a theorem quantifying over `denoteR`'s
  sites, which would be an induction over the elaboration (not attempted).
- **Fixtures** (`Test/Program/ScopeMarkers.lean`, imported after `DenoteRContract`):
  `guardR_not_algebraic` (`:26`, P5's red control), `erasure_runs_skipped` (`:44`, red: a
  continuation into `unit` does not pass a skipped failure through, and for it the erased scope
  is not the taken-only sequencing), `seq_reads_taken` (`:61`, positive: `denoteR`'s
  sequencing shape meets the premise), and two `#guard_msgs (error)` fixtures (`:79`,
  algebraicity refused by computation; `:91`, the taken-only law refusing `toUnit` at its
  premise). All three theorems print `[propext, Quot.sound]`. The frozen contract already pins a
  related scope-versus-bind control (`cleanup_boundary_distinct`,
  `Test/Program/DenoteRContract.lean:240`, verifier ALG-12); this one is generic over the body.
- **Commands.** `lake env lean -DwarningAsError=true` on `ScopeMarkers.lean` and on `DenoteR.lean`
  (no output); `lake build Effect4.Laws.Program.ScopeMarkers` (240 jobs, success, after the first
  wording of the docstring edit, so `DenoteR`, `InterpR` and `EvaluateR` rebuilt within it; the
  amended wording was checked by `lake env lean` and is rebuilt by the final build); the fixture by
  `lake env lean -DwarningAsError=true` (exit 0, axiom lines only). `DenoteR.lean`'s other
  dependents see a docstring change only (AGENTS.md: no dependent build owed); the final build
  covers them.

### Landing 7: the `seqR` sequencing lemma (commit `35277f40`)

- **Source.** The coordinator's port `docs/research/2026-10-01-landing/ports-at-dceae006/HeadBindGuard.lean`
  (the verifier's `verify-BindGuard.lean` with exits read through H2's `ExitOk`); its log
  `port-HeadBindGuard.log` was not in that folder when read, so the port's statements were
  re-established here by elaboration. **What the merge changed, restated:** `TypedProg.pure`,
  `unguard`, `finishFinalizer`, `scopeExit` payloads and the guard's `run`/`skip` clauses carry
  `ExitOk` (= `FitsExit ∧ NoShapeDefect`), so `seq_typed` reads `hfit.1` for membership and
  hands `hfit.2` through on the skipped failure (`NoShapeDefect` ignores its type). Meaning kept:
  the statements are the verifier's with `FitsExit` replaced by `ExitOk` at the typed exit
  positions; `seq_typed`'s value premise stays at `Fits w' v mid.answer`. No statement failed to
  hold.
- **Theorems** (new `src/Effect4/Laws/Program/Typed/Seq.lean`, imported from `Laws.lean` right
  after `Typed.Residual`): `close_typed` `:40`, `seq_typed` `:59`. **Proved**, both
  `[propext, Quot.sound]`.
- **Fixtures** (`Test/Program/TypedProgBindRed.lean`, from landing 1; now imports `Typed.Seq`):
  `catchNat_typed` `:85`, `toUnit_typed` `:96`, `bind_not_typed` `:106` (red: the guard's skip
  clause sends `nat 1` past the continuation), `guard_bind_not_closed` `:120` (red, the
  existential shape), `seq_sample` `:130` (green: `denoteR`'s shape typed by `seq_typed`), and
  the skip clause refusing the body's success at `unit` pinned under `#guard_msgs (error)`
  `:146`. All print `[propext, Quot.sound]`.
- **Coordinator's message on landing 1's red control.** "P6's `typedProg_not_bind_closed` no
  longer elaborates on the merged tree; use the port's `bind_not_typed` and
  `guard_bind_not_closed`": both are now fixtures (above). P6's control was not dropped: landing
  1 restated it against `ExitOk` (continuation premise `ExitOk w' mid ex`, payload via
  `strongExit_success`) and it elaborates at `dceae006` (**proved**, `[propext, Quot.sound]`,
  `TypedProgBindRed.lean:32`); it is the bare-marker refutation, the port's two are the
  guarded one.
- **Literature wording corrected** (verifier ALG-04): both headers now cite the principle that
  non-local control flow breaks the bind rule (Timany and Birkedal as de Vilhena §2.4 cites
  them, read in the papers review G8); Hazel's neutral-context rule is called a loose analogy.
- **Commands.** `lake env lean -DwarningAsError=true src/Effect4/Laws/Program/Typed/Seq.lean` (no
  output); `lake build Effect4.Laws.Program.Typed.Seq` (362 jobs, success); the fixture by
  `lake env lean -DwarningAsError=true` (exit 0, axiom lines only).

### Landing 8: provision (commit `74db2bd2`)

- **Coordinator's narrowed scope** (message during the run): Codex's item G already removed the
  stale `build_total` header; fix only `:120` ("join associativity owed") and `:162` ("the
  adjunction"), and land `provideMerge_assoc`, `provideMerge_assoc_rows` and `provide_provide`
  with the error column. Done as below; the third stale text met in the same file ("the
  specification `build` and its totality", `:219` at `dceae006`) is corrected under landing 9.
- **Home, split by root.** `Program/Provision.lean` is in the core root, which must never import
  the proof graph, and the error column needs `Ty.join_assoc` (`Laws/Program/TypeAlgebra.lean:433`).
  So `provideMerge_assoc_rows` (rows only) went beside `provide_provide_rows` in the core file,
  and the whole-type laws went to a new `src/Effect4/Laws/Program/Provision.lean` (imported from
  `Laws.lean` after `TypeAlgebra`; it continues the `Effect4.Program.Provision.LayerTy`
  namespace, as the law modules continue their definition modules').
- **Theorems.** `Program/Provision.lean`: `provideMerge_assoc_rows` `:143` (at the head).
  `Laws/Program/Provision.lean`: `provideMerge_assoc` `:32`, `provide_provide` `:45`. **Proved**,
  each `[propext, Quot.sound]` (`Ty.join_assoc` itself prints the same).
- **Texts.** `provide_provide_rows`'s docstring (`:119-127` at the head) says the statement is
  over the rows because the core module does not import the proof graph, cites `Ty.join_assoc`
  and the whole-type `provide_provide`, and names the red control. The section header (`:185`
  at the head) reads
  "Satisfaction is inclusion into `keysRow`", with one sentence: one monotone map, so a
  representability statement, not an adjunction (A11).
- **Fixtures** (`Test/Program/ProvideRows.lean`, imported after `ProvisionContract`):
  `a_needed_nested` `:29`, `a_discharged_sequenced` `:35`, `provide_not_assoc` `:45` (P7's red
  control), `provideMerge_regroups` `:51` and `provide_sequenced` `:57` (positive, same layers),
  and `decide`'s refusal of plain associativity pinned under `#guard_msgs (error)` `:67` (the
  kernel evaluates both rows and finds them different). All print `[propext, Quot.sound]`.
- **Commands.** `lake env lean -DwarningAsError=true src/Effect4/Program/Provision.lean` (no
  output); `lake build Effect4.Program.Provision Effect4 Effect4.Laws.Program.Folds.Provision
  Effect4.Laws.Program.Provision` (332 jobs, success; the core root `Effect4` and the fold
  connector are the core module's direct dependents); the fixture by `lake env lean
  -DwarningAsError=true` (exit 0, axiom lines only).

### Landing 9: stale texts (commit `25d2561e`)

Comment and docstring edits only, in files no other seat's brief names (each elaborated by
`lake env lean -DwarningAsError=true`, no output; AGENTS.md owes no dependent build for them):

1. `src/Effect4/Program/Provision.lean`, header bullet on `build` (`:35-41`): adds that
   `build_total` was cut as unused at `b08f3b58` and its restoration is owed under R5 (the
   synthesis's §4.5 item 9: "'owed under R5' may still be added"; the brief's text item).
2. Same file, the layer language section (`:219` at `dceae006`): "the specification `build` and
   its totality" (stale: the totality theorem is gone, traversal census line 436) now reads "the
   specification `build` (its totality is owed; see the header)".
3. `src/Effect4.lean:111` (a comment at the `Effect4.Program.Provision` import, not an import
   line): "the build specification with its totality theorem" now says the theorem was cut at
   `b08f3b58` and restoring it is owed under R5.
4. `src/Effect4/Laws/Effects/Protocol.lean` header: named the tree's protocols as "`progress`'s
   hypotheses and conclusion" and "`OpOk`/`AnswerOk`"; `OpOk` exists nowhere in `src/`
   (grep), and `AnswerOk` now names a decision's admission (`Typed/Assembly.lean:150`). It now
   names `Ψ_S` (31 rows), `Ψ_F` (40 rows) and `TypedProg` (`Typed/Residual.lean`), and says the
   generic laws are owed separately for `TypedProg`.
5. `src/Effect4/Laws/Program/Iter.lean` header: "It is Elgot iteration cut at a budget" gains one
   sentence: each budget is one approximant of the least fixed point; Elgot's laws hold for the
   limit and for no single budget (`IterLimit.lean`). Not false before; the algebra note §2.3
   reads the budgeted meaning as "not an Elgot algebra", and the sentence keeps a reader from
   applying an Elgot law at a budget.

Left alone, as the brief says or because they are not source: `guard_inv`'s "exactly"
(`Typed/Residual.lean:231-232`, seat B's); the model-probe synthesis's "machine as runner"
(`:730`) and "adjunction" (`:318`, `:949`), which are research history, not authority; the
coherence principle's "(row 38)" (`docs/core/coherence-principle.md:568`), which the verifier
showed is correct (ALG-19 refuted A12).

### Fix after the final build (commit `a1541c86`)

- **First final build** (`LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` at `25d2561e`,
  6 min 3 s): every module built except the root `Effect4.Laws`, which failed at its import of
  `Effect4.Laws.Program.ScopeMarkers`: "environment already contains
  `Effect4.Program.Sched.guardR_bind.match_1` from `Effect4.Laws.Program.Intro.Prepare`";
  `Test.All` was not reached. Cause: P5's scope law is already in the tree
  (`Laws/Program/Intro/Prepare.lean:44`, same statement with `unguardTail`); each module
  elaborated alone, and only the root imports both.
- **Fix.** `ScopeMarkers.lean` drops its copy and imports `Intro.Prepare`; its header cites the
  existing theorem; the fixture's red control rewrites with it. Then `lake build
  Effect4.Laws.Program.ScopeMarkers` (310 jobs, success) and the fixture by `lake env lean
  -DwarningAsError=true` (exit 0, axiom lines only).
- **Name scan.** Every declaration name landed in `src/` by this seat was grepped as a
  declaration across `src/` and the pinned `Effects` package: only `guardR_bind` had a second
  site. Test declarations live in per-file `Test.*` namespaces; the nine new ones are each
  declared once (grep).
