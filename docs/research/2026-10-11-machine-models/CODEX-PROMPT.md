# Prompt for Codex: consolidate the goals lane on shared accounting laws

Work in the lean4-effect4 repository. Base: your integration branch, rebased on
`refactor/phase1-phase3` at the commit that adds this file or later. Read `AGENTS.md` first; it binds
you. Then read this folder's `README.md` and the earlier note
`../2026-10-11-machine-from-the-base/README.md`.

## The one thing to know first

**Newest, 2026-10-11 22:15: the landing waits for your ambient migration.** The landing branch
`land/typed-context` (`8f1f3d1ac`) has merged your head at `fcac7de73`. It carries everything outside
`Laws/Program/Typed/`:

- the template rows: `Effect.context<R>()`, where `R` is the requirement row's type, and
  `Effect.provideContext(self, context)`;
- the exact row reader (`readKeys`, `readKeys_requirementType`, `readKeys_exact`);
- the TypeScript reader, both foreign recognizers and the OCaml bridge;
- the tests, and the laws that the new names and thunks reach outside `Typed/`.

Its law graph builds except `Typed/Assembly.lean`, which your receipt names as open
(`codex/context/SourceArgumentsReceipt.md`). Finish Body, LayerArm and Assembly on the seat, and
keep to `Typed/`. Claude merges each new seat commit into the landing branch. The landing goes
into `refactor/phase1-phase3` when `Effect4.Laws` builds there.

**Earlier, 20:20: Claude is landing `codex/symbolic-native-fold` at `e30a74131`.** The
owner asked for it. The landing branch is `land/typed-context`, in its own worktree. It reconciles
the seat with R2 and items 10 to 12. It also does the plan's target lane: template rows for
`Effect.context<Row>()` and `Effect.provideContext`, the reader, the TypeScript reader, and the
generated and OCaml sweep. Do not redo the target lane on the seat. After the landing merges into
`refactor/phase1-phase3`, merge it into the seat before its next commit.

**Earlier, 18:30: items 10 and R2 are merged; item 11's first two steps landed beside you.**

- R2 merged by fast-forward at `6c4bb709d` (`AUDIT.md`, section 15:40: improving in structure,
  private analyses flat). `E4-RUN-CE-046` is repaired; its behaviour gates are owed at the sweep.
- Item 10 has landed in full (`AUDIT.md`, section 18:30): one footprint function, one frame
  theorem, one `RunMachine.dropToken` and one `RunMachine.observe`. Next: item 12 as your plan
  has it, then item 11's caller moves below.
- Item 11, steps 1 and 2, landed at `58e25fd59`, with no existing module edited:
  - `Effect4.ListRel` (`Laws/Data/ListRel.lean`) carries `Book.lean`'s lemmas under their names
    and statements. `Laws/Data/ListRelConnectors.lean` connects `Machine.ListRel`,
    `Modules.Pointwise` and `Program.Fits` to it.
  - `Laws/Store/Names.lean` holds names, correspondences, `Rel`, `cata_val_related`, the
    support and renaming folds, `Rel.mono`, `validIn_iff_diag` and `Parametric`.
- Your next steps in item 11, in order:
  1. Delete `Book.lean`'s `ListRel` in a slice that touches `Book.lean` anyway: 190 modules
     rebuild once. Inside `namespace Effect4.Machine` the name then resolves to
     `Effect4.ListRel`, so callers do not change. Rename only qualified `Machine.ListRel` uses.
  2. Move `Pointwise`'s 23 uses to `ListRel`; keep `Fits` through `fits_iff` until a slice
     touches `Typed.lean`.
  3. Make `Val.validIn`'s theorems corollaries of `validIn_iff_diag`.
  4. Then steps 3 to 9 below. `FiberEdit.keys`, the 49th hand support function, is step 4's
     first carrier.

The 11:25 build break is repaired (`98567f7f2`). Its rule stays: a slice that changes
`src/Effect4/Machine` builds `Effect4.Laws` whole before it commits.

The goals lane re-builds the same structures per weight and per scenario, about 44,000 lines in two
days.

- **Four ledgers each re-prove the same three things:** per-arm debits, edit transport and a
  thirteen-field `DecisionLift`. The ledgers are `ReleaseCustody.Control.Funded`,
  `FinalizerCredits.Funded`, the source-opportunity budget and Atomic `WriterPhase`.
- **The Timeout chain re-does every command and evaluator arm**, over 36 files. Its open numeric
  producer would do them a third time.

**Read `AUDIT.md` in this folder at the start of every slice.** Claude appends to it at each merge,
and its newest section names the regressions to replace first.

**Stop adding per-scenario machinery.** Each new fact goes into a shared structure below, or is an
instance of one. Speed rules (owner, 2026-10-11): narrow builds and `#axiom_audit` per slice.
Behaviour gates only where a slice changes executable code, and then at a sweep.

## What lands beside you (verify, do not trust)

- **L1, the stack ledger (landed).** A place invariant whose places are the saved stacks:
  - `src/Effect4/Laws/Machine/Ledger.lean`: `StackLedger` (frame-event weights `produced` and
    `consumed`, a finalizer program's start `program`, a stack weight `stack` with `empty`),
    `Funded`, and `Same` with the edit laws proved once (`same_emit`, `same_update`,
    `same_modify`, `same_map`, `same_spawn`, `same_start`, `same_forkFinalizers`,
    `same_countdown`, `same_beginRace`, `same_postTask`, `same_drainOwed`,
    `same_interruptUpdate`, `same_linkScope`, `same_interruptEach`);
  - the same module also holds the frame rule over distinct ids (`update_bound`) and the
    evaluation bridge (`IterDebit`, `IterKept`, `Balanced`, `settle_balanced`, `IterKept.rebase`);
  - `src/Effect4/Laws/Program/LedgerRun.lean`: `Kept` (what a ledger supplies: its evaluation
    debit, and that the race's cancel frame and the parallel close's iterator add no weight),
    `command_funded` (every command), `edits` (every edit outside the loop), `stepped`,
    `funded_reachable` (every reachable machine);
  - `src/Effect4/Laws/Program/LedgerFinalizer.lean`: the finalizer ledger as the first instance.
    `funded_iff`, `iterKept` and `kept` connect it, and `funded_reachable` re-derives
    `FinalizerRun.funded_reachable` with no command case of its own;
  - audit: 190 declarations within `[propext, Quot.sound]`.
  - Limit: a weight that reads the current code (`SourceOpportunities.frame`, Atomic
    `WriterPhase`) is not a stack weight. Its interrupts and stale write-backs need R2 first, or
    an `outside` argument as today.
- `Test/Counterexamples/Machine/Semantics/SelfInterrupt.lean` (`E4-RUN-CE-046`, seeded): a fiber
  that interrupts itself through its own handle runs to a frontier. On rc.112 it exits interrupted.

## The work, in order

1. **Timeout, before the numeric producer.** Write the producer of `Numbers` and `Declared` over the
   shared laws, not over a third command pass.
   - Other fibers: `Interferes`, `iteration_interferes` and `driveStep_framesFollow`/`Transports`
     (`Laws/Program/{Interference,CommandFrames}.lean`).
   - The pre-count entry prefix: `StackRegion` and `LiftPrefix`, with the attempt's `onExit` frame
     as the region's entry. They replace the 4 + 1996 split of the budget.
   - The counts: `Ledger` (L1).
   - Then, keeping names and statements, as consolidations:
     - `ReleaseCustody/NativeStacks` (`native_links`, `iteration_links`) as a corollary of
       `iteration_interferes` and `StackRegion.other_edits_stack`, as `NativeMachineShape`
       already does;
     - `HostTimeoutFlow` and most of `HostTimeoutFrames` as instances of `Machine/AnswerFlow`;
     - `HostTimeoutRaceSteps.after_exit_*` citing the `RaceFirst` laws.
2. **L2, labelled moves.** Label each `FrameMove` by the events it emits: `step` and `finish`
   carry them already; a pop carries the popped frames and the hooks. Then:
   - prove `iteration_moves` with the labels, so that the iteration's events are the labels'
     events;
   - prove `Moves.balance`: a weight that each move changes by at most its label's gain less its
     cost changes along a word by the sums;
   - prove one pop law, `getCont_spec`: the stack is the popped frames over a rest, the new stack
     is the hooks over that rest, and the answer is a popped frame, a hook's replacement, or none.

   Then replace the pop-chain copies (`passPushed`, `joinPushed`, `popFrom`, `getCont`,
   `resumeValue`, `resumeCause` re-walked for about 20 predicates) by instances. Do
   `FinalizerCredits` first: it is an exact instance of `FrameWeights`.
   - **The store through the labels (audit, 2026-10-11).** A `step` label holds the code it ran,
     and a store step's code is `sync (op o)`. Define the cells a word writes as the homomorphism
     from labels to `(Finset RefKey, ∪)` through `o.refKernel`. Prove one law: the iteration's
     store is its executed operations folded over the store before. With
     `RefKernel.refWriteBack_peek_other`, a cell outside the written set keeps its value. That
     lift replaces each scenario's writer-census premise
     (`../2026-10-11-tokens-in-places/model-first.md`).
3. **The ledgers as instances of L1.**
   - First delete what `LedgerFinalizer` makes redundant: `FinalizerCommands`' command proof and
     `FinalizerBookkeeping`'s edit lemmas, keeping their names as one-line instances.
   - `FiberSum` (`src/Effect4/Laws/Machine/FiberSum.lean`, landed): a weight summed over the fiber
     table and its frame rule (`split`, `outside_update`, `outside_update_le`, `install`,
     `update_bound`, `update_debit`). `FiberSumConnect` shows by `rfl` that the source-opportunity
     sums, the writer weights, release custody's fiber part and the stack ledger's holdings are
     instances. Replace each family's own split lemmas by `FiberSum`'s, keeping names and
     statements.
   - Then each stack-weight ledger (`ReleaseCustody`'s stack credits, the release and log
     ledgers): define its `StackLedger`, prove `Kept`, and take `funded_reachable`.
   - The current-code weights (`SourceOpportunity`, `WriterPhase`) move after R2, or with a
     frame-weight generalization of `Ledger` (the stack weight plus the current code), proved the
     same way.
   - Then state the open goals `Workers.logs_step`, `QueueWorkers.logs_history` and
     `Atomic.Cleanup.log_debits` as ledger instances, and prove them.
4. **L3, code weights as one fold.** Native code has no generated algebra, so about 25 hand folds
   (`stackCredits`, `below`, `WriterPhase.name`, `SourceOpportunities.thunk`, …) walk it by hand.
   - Generate the fold (the one-generator rule, `docs/GENERATED.md`).
   - Make each weight a table of leaf weights.
   - Probe first `Control.stackCredits`/`stackCap`: its `afterScopeAdd` credit depends on the active
     response, so it is not additive.
5. **R2, edits as messages** (repairs `E4-RUN-CE-046`; a machine change).
   - An iteration's edits of another fiber's record (`observe`, `filterObservers`, `interrupted`)
     become a list that `settle` applies after the running fiber's write-back. An edit of the
     running fiber itself then reaches it.
   - Probe the other aliasing arms first: the join park, `countdownPark` and `linkScope` on the
     running fiber.
   - It changes executable code: regenerate what it reaches, run `check-truth` and
     `check-compiler` at the sweep, and turn the counterexample's attack guard into the repaired
     regression.
   - **Coordinator review, 2026-10-11 11:25: approved as written.** The plan
     `docs/research/2026-10-11-codex-r2-message-plan.md` sharpens this item. The messages apply
     after the local write-back and *before* the outcome disposition, not after the whole
     `settle`. The three tags `observe`, `dropToken` and `interrupt` are first-order data. Its
     seven pinned cuts are the regression set. Proceed with its migration steps 1 to 12 in the
     machine-structure lane. State the selected-owner retention as a premise; no `getD`
     fallback. Behaviour gates run at the sweep, as the plan says.
6. **R1, R3, R7** (`README.md` §3).
   - Cut `Resume.continueWith`, `Dispatcher.armed`, `Pending.waitingOn`, the five dead
     `RaceAllState` fields and `Race.settled`. Make `finalizing` a `Bool`. `RaceAllState.initial_eq`
     is a frozen census law: propose its amendment in the receipt.
   - Read the yield budget from `budgetOf` and drop the fiber's copy.
   - Cut the scheduled wake branch, or record why it stays.
7. **Context writes as a typed region** (decisions row 349, option A, ruled 2026-10-11; repairs
   `E4-CTX-CE-001`). A program-syntax change: follow the new-constructor checklist (the generated
   families, the LCNF roots, the golden tree, the OCaml bridge, the compatibility and case
   policies).
   - Replace the raw `setContext` and `getContext` actions with rc.112's `context` reader, whose
     type carries its row, and the `provideContext c body` region, which removes `c`'s keys from
     `body`'s row (`../2026-10-11-machine-from-the-base/context-transformers.md`, §4 and §6).
   - Then B6, the services' chain (`CtxChain`), and a definition's context transformer per
     parameter.
   - It changes executable code: regenerate what it reaches and run the gates at the sweep. Turn
     `E4-CTX-CE-001`'s attack guards into the repaired regression.
   - **The region is an instance (audit, 2026-10-11).** Compile `provideContext` to a frame that
     restores the context on every exit. Prove its bracket as an instance of
     `MaskBracket.compiled_region_bracket` and `StackRegionRun.compiled_region_bracket_of_prefix`,
     not as a new region law (`../2026-10-11-tokens-in-places/README.md`, F1).
8. **Housekeeping: worktrees** (owner, 2026-10-11: worktree cleanup; the disk has 15 GB free).
   The module-design-review worktree is gone. Survey of 14:05, `refactor/phase1-phase3` at
   `0d2687767`:
   - **Merged and clean; remove each, then `git branch -d`:** `unguard` (3.3 GB),
     `module-semaphore` (2.5 GB), `prepared-run-view`, `live-graph-index`, `live-graph-routes`.
   - **Idle since 2026-10-08, every commit's subject already in the integration branch:**
     `module-authoring`, `module-construction`, `module-field-inference`, `module-folds`,
     `step-captured-folds`. Check each with `git cherry`, then remove the worktree.
   - Run `git status --short --ignored -- docs/research` in each tree first: research files are
     ignored, and a removal loses them.
9. **L4 to L6** at any time: `AppendOnly` and `FreshSupply` for ids, keys and tokens; `Census` and
   `Linear` for the static site analyses. Reconcile `OncePlaced` with `Linear` in the receipt.
10. **Machine edits: one word per helper, one fact per edit** (audit, 2026-10-11; the design,
    census and order are `../2026-10-11-tokens-in-places/machine-edits.md`). Sixteen law modules
    re-prove their invariants through every driver helper, about 210 helper lemmas. Make each
    helper a word of primitive edits, proved once, and each invariant a fact per edit.
    - The probe `../2026-10-11-tokens-in-places/probes/MachineEdits.lean` compiles. `spawn` is its
      word by `rfl`, and `start` and `postTask` by one case split. Trace growth and the frame rule
      hold for every word by one induction each.
    - Steps 1 to 4 of the note's §4 do not touch R2's helpers: the alphabet, the R2-free
      decompositions, the `Approximation` pilot, then `Ledger.Same`. R2's migration delivers its
      helpers' words (step 5). Then `MaskRuns`, `Handles` and the guard modules move.
    - **Sixteen edits cover every driver write** (census, 13:35). Each `{ m with … }` write in
      `Machine/Fibers.lean` sets one field, or splits into one-field edits. Your draft's tags are
      exactly those writes.
    - **One footprint function.** Each edit writes one field of `RunMachine`. So give the
      alphabet `Edit.writes : Edit → MachineField`, an eleven-constructor enumeration, and one
      frame theorem: an edit keeps every field but the one it writes. `missesFibers` becomes
      `e.writes ≠ .fibers`. `stateWrite`, `events` and the eighteen field rows of `Keeps.lean`
      become instances. `settlementWrite` stays a sub-alphabet, because `appendFiber` also writes
      the fibers.
    - **Per-edit obligations come from `#frame_rules`.** For an invariant that is a structure
      predicate over the machine, `#frame_rules` (now with `(state := …)`) generates one rule per
      field. An edit's obligation is the rule at `e.writes`. So the matrix of invariants by edits
      is generated, and only payload facts are written by hand.
    - **One `dropToken`.** The observer filter is written three times in `Machine/Fibers.lean`:
      `applyFiberEdit`'s `dropToken`, the `dropObservers` arm of the `withFiber` dispatch and
      `dropObservers`. Your `Edit.apply` writes it a fourth time. Define `RunMachine.dropToken`
      once beside `update`, and use it in all four places.

11. **Handles: names, worlds and one relation** (theory 2026-10-11; the model, census, probe and
    order are `../2026-10-11-handles/README.md`). Start after R2 commits and item 10's alphabet
    lands. The probe `../2026-10-11-handles/probes/Names.lean` compiles and audits clean.
    1. **One pointwise relation first.** The tree has two: `ListRel` (`Laws/Machine/Book.lean`)
       and `Pointwise` (`Laws/Step/Reading.lean`). Move one to a low shared module, make the
       other a connector, and build on it. The probe's `ListRel` is a third and does not land.
    2. **`Rel` and the abstraction theorem for `Store.Val`.** Land the probe's §§3 to 6 as a
       module under `Laws/Store/`, with `validIn_iff_diag`. Then `Val.keys` goes
       (`handles_eq_cata`), and `Val.validIn`'s sixteen theorems become corollaries of the
       diagonal.
    3. **The generator emits it.** `tools/Effect4Gen/Fold.lean` emits, per signature, the support
       fold, the renaming fold, `Rel`, and the abstraction theorem beside `hom_eq_cata_val`.
    4. **The machine carriers get `Rel`.** The 48 hand support functions of `Handles` go,
       carrier by carrier, each with a connector first.
    5. **One world.** A partial bijection of names, with an optional type on each pair. The three
       orders (`Machine.World.le`, `Stores.le`, `Program.Typed.World.le`) become one, and the four
       ghost tables become one table keyed by name.
    6. **`KeyBounded` as two shapes.** Its 34 support bounds become parametricity of the hooks.
       Its nine store steps become one monotone store-step definition with a composition law.
    7. **The handle invariant per edit.** With item 10's words, `MintedAt` owes one fact per edit.
    8. **DET-3 `names-equivariant`**, per edit, from `Parametric.equivariant`. The fiber table
       relates as a finite map: `../2026-10-11-handles/probes/Tables.lean` proves lookup, update,
       append and pointwise map for it, generic in the relation on fibers.
    9. **A protocol state per name** (the note's §2.9). Each kind declares its forward order, and
       each store operation proves once that it moves forward. `probes/Protocols.lean` does it for
       the Deferred store. Typing monotonicity and the stable facts (completed, closed, exited)
       then need no per-step lemma.
    - Keep every existing theorem's name and statement; connectors first, then callers, then the
      old proof goes. Report lines before and after each step.

12. **Types across the faces: `mul` and the OCaml ingress** (the owner, 2026-10-11: tighten the
    type interface between Lean, TypeScript and OCaml; the note is
    `../2026-10-11-type-interface/README.md`). Two items are in your lane; take them after item 10.
    1. **`mul` through the profile** (`E4-RUN-CE-047`, seeded; the note's R-T2). Lean's
       `NativeAtom.eval` answers the exact product, the TypeScript prelude rounds above 2^53, and
       `lcnf_nat_mul` saturates above 2^62. Mark it as row 321 marks `add`: a `Profile.scale` in
       `Machine/Integers.lean`, its OCaml row through `E4_clock`, and `to_profile_nat`. Or remove the
       atom, as row 309 says; `Test/Dogfood/P1HttpCache.lean` is its one user. Propose which in the
       receipt.
    2. **The OCaml ingress** (the note's R-T8). `E4_engine.answer_async_success` builds `Val_nat` from
       any `int`, so a negative natural passes reply admission. Refuse it, refuse a float that
       `Val_float` cannot hold, and turn warning 8 back on in `LcnfGen.lean`'s header. Each is a
       finite control in `dune test`.

## How to work

- Place every obligation before you work it (AGENTS.md, Trust). Each shared law's placement is
  concept `reactive-scheduling` or `scope-lifetime-finalization`, as the instance it replaces.
- A consolidation keeps each replaced lemma's name and statement, so no consumer moves. It removes
  the old proof in the same commit. Report the lines removed (`wc -l` before and after).
- Arm by arm, as `Moves.lean` does: `split`, `cases`, `exact`. No `repeat' first`, `first`, `try` or
  `simp_all` in new or touched proofs.
- Do not edit `docs/core/decisions.md` or `lakefile.toml`; propose rows in the receipt.

## Deliverable

A receipt per slice, `docs/research/<date>-codex-consolidation-receipt.md`, or a section added to
the running one. Each receipt gives:

- first, the one thing to know before merging;
- base and head;
- the changed files;
- the commands and their results;
- the audit output;
- the lines removed;
- the open goals.

Never push. Commit by explicit paths; `git add -f` for `docs/research`.
