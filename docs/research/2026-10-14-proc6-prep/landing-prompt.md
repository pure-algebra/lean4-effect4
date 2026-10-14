# Codex: land PROC-6, the machine runs a definition block as its block meaning

Status: brief (history, not authority). From the coordinator, 2026-10-14, for the landing seat.
The plan is locked: `docs/research/2026-10-14-proc6-scout.md`, fifth version, and decisions row 379
(`docs/core/decisions.md`). You reviewed versions 4 and 5. Your findings F1 to F4, N1 and N2 are
folded in, and §11 of the plan gives each one's disposition.

## The one thing to know first

The plan changed after your review of the version-5 amendment. N1 showed that a default-budget
invariant over budget-safe values is false. The plan does not repair that invariant. It drops it.
Ruling 5: the machine is proved at every scheduler budget the fibers' contexts set, with agreement
conditioned on a finished run (`flush_Myield`'s receipt) and no progress claim. So `DefaultBudgetCtx`,
`BudgetSafeVal`, `ContextFreeTy` and the reserved-key rule appear nowhere. The fragment restricts no
row column and no service key. If you find that ruling 5 cannot be proved as stated, stop and report
with evidence. Do not reintroduce an invariant.

## Read first

1. `AGENTS.md`, in full. Its Trust and Working sections bind every slice.
2. The locked plan, all of it. Its stages are your slices' content. Its §2 is the source map, and its
   §7 is the placement of every goal.
3. Decisions row 379.
4. `docs/research/2026-10-14-proc6-prep/README.md`: the coordinator's preparation, the measured
   fan-out and the baseline gate results at the base commit.

## Where you work

- Base: the commit that locks the plan, on branch `refactor/phase1-phase3` of
  `/Users/pooks/Dev/lean4-effect4`. Its hash is in the prep receipt.
- Make your own worktree and branch:
  `git worktree add /Users/pooks/Dev/lean4-effect4-codex -b codex/proc6 <base>`, then
  `cp -c -R .lake/packages /Users/pooks/Dev/lean4-effect4-codex/.lake/packages`, then one
  `lake build Effect4 Effect4.Laws` there (cache hits).
- Never copy `docs/research` into the worktree. Write your receipt in the main checkout's
  `docs/research/2026-10-14-proc6-prep/landing-receipt.md`, or in your worktree and force-add it.
- Do not edit `/Users/pooks/Dev/lean4-effect4-gemini` or the main checkout's source. The coordinator
  merges your branch.

## The rules that bind every slice

- Build only through the slot: `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`.
  One lake at a time across the machine.
- Iterate on a module with `lake build <thatModule>`, which builds its imports and not its dependents.
  Build the dependents once, when the slice's edits are done (§ "The build plan").
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern`, `implemented_by`. No `sorry` except as a
  planned goal's body (`proof_goal`, decisions rows 203 and 207). Every warning is an error.
- In `src/Effect4/Laws/**`: `aesop` and its banks. No hand-written `simp_all`, `first | …` or `try`.
  Every hand-written `simp` is `simp only [...]`.
- Place before you prove (AGENTS.md, Trust): every new theorem names its concept, its registry
  claim, its consumer, its reach and what it does not establish. The plan's §7 gives them.
- A deleted theorem moves its `@[semantics …]` placement onto its survivor.
- Audit each slice's modules with `#axiom_audit M …` (`tools/ProofGraph/AxiomAudit.lean`), never with
  `#print axioms`. The gate is `[propext, Quot.sound]`, with `sorryAx` only as a goal's own body.
- Commit by named paths, one slice or one coherent part of a slice per commit. Never `git add -A`.
  `docs/research` needs `git add -f`. End each message with the attribution lines your harness gives.
- Never push. Download nothing. Never write `2>/dev/null`. Run bun only as `bun --no-install`.
  tsgo 7 is the one TypeScript compiler.
- `lakefile.toml` and `docs/core/decisions.md` are the coordinator's. Edit the root imports
  (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) and `Test/Audit/AxiomGate.lean` only by
  appending at their ends. Propose a decisions row in your receipt; never write one.
- Regenerate what a change reaches: `make gen-lcnf` after the compile changes, then
  `opam exec --switch=effect4 -- dune build` from `ocaml/`; the semantics report (`make gen-semantics`) after a placement
  or registry change (`docs/GENERATED.md` names its producer).
- Temporary files go in a scratch directory of your own, never in the repository.

## The build plan

The prep receipt measures each module's dependents. Three numbers set the order: a change to
`src/Effect4/Program/Compile.lean` rebuilds 404 `Effect4.*` modules, one to `Agreement.lean` 252, one to
`Agreement/Machine.lean` or `Agreement/Segment.lean` about 188. The leaf modules rebuild a handful.

1. **Group every edit to a high-fan-out module into as few builds as possible.** Slice A holds stage
   0a and stage 1's premise swap, and is built once.
2. **New material goes into new leaf modules**, appended to the root imports. A proof slice then
   rebuilds its own module and the root only.
3. **Stage 4 must edit the hosted spine.** Edit bottom-up (`Agreement/Machine.lean`, `Segment.lean`,
   `Calls.lean`, `LoopCalls.lean`, `Hosted.lean`, `HostedLoop.lean`, `Api/SessionMeaning.lean`,
   `Api/SessionMeaningLoop.lean`). Build each with `lake build <thatModule>` as you go, then the
   dependents once.

The leaf modules, proposed names:

| Module | Content | Stage |
| --- | --- | --- |
| `src/Effect4/Laws/Program/BlockMeaning.lean` | `TreeB`, `ParamTreeB`, `BlockCarrierB`, `provided`, `blockAlgB`, `denoteBlockB`, `hostRunBlockB`, the laws; `mapOps` and `blockOf?` moved here | 0 |
| `src/Effect4/Laws/Program/FragmentBlock.lean` | `BodyRows`, `BlockRows`, `bodiesOf_blockRows` | 1 |
| `src/Effect4/Laws/Program/Agreement/BlockPlain.lean` | `PlainHooks.of_blockRows` and its plainness arms, beside `PlainHooks` in `Machine.lean` | 1 |
| `src/Effect4/Laws/Program/Agreement/Blocks.lean` | `ParamsAgree`, `CompilesBlk`, `compilesBlk`, `compilesBlk_root`, the address lemmas | 2 |
| `src/Effect4/Laws/Program/Agreement/HostedBlocks.lean` | the closing steps on blocks | 3 |
| `src/Effect4/Laws/Api/SessionMeaningBlocks.lean` | `H9Blocks`, `h9_blocks` | 3 |
| `src/Effect4/Laws/Program/ValidatedBlocks.lean` | `conforms_sat` and `agrees_hostRun` on blocks | 3 |

You may rename or merge them. Keep each a leaf of the import graph, and record the final names in
your receipt.

## The slices

Land them in this order. Each ends with its narrow build, its `#axiom_audit`, the gates it reaches,
its commits and its receipt section.

### Slice P: placement

- Add the registry claim `rows-block-host` (`tools/ProofGraph/Registry.lean`), concept
  `translation-simulation`, role simulation, beside `rows-loop-host`.
- Create the leaf modules of stages 0 to 3. Write stage 0's definitions in full: they are the
  meaning, and every goal states over them. Write `BodyRows`, `BlockRows`, `ParamsAgree`,
  `CompilesBlk` and `H9Blocks` too.
- State every goal of the plan's §7 for stages 0 to 3 as `@[semantics "translation-simulation"
  (requirement := …)] proof_goal …`, with its consumer in the docstring. Stage 4's goals are placed at
  the start of slice F, since they state over the reworked machine forms.
- Build the leaf modules, regenerate the semantics report, and run `#plan_status` on
  `rows-block-host`. Commit.

### Slice A: the high-fan-out edits, built once

- **Stage 0a**, all of it (the plan's §5): the `call` frame in `suspendBodyAt`; `denoteEffBody` and
  `denoteR_perform`; `suspendBodyAt_call`; `intro_call` onto `weight_redirect_params_lt`, then delete
  `weight_redirect_call_lt`; the typed `call` arm; the `Point.params` docstring.
- **Stage 1's premise swap**: the structure `PlainHooks` in `Agreement/Machine.lean`,
  `PlainHooks.of_loopedRows`, and `(hroot : PlainHooks root)` in the 23 statements of `Machine.lean`,
  `Segment.lean`, `Hosted.lean`, `Api/SessionMeaning.lean` and `Api/SessionMeaningLoop.lean`. Callers
  that hold `LoopedRows` pass `PlainHooks.of_loopedRows`.
- **Stage 4's flag-general lemmas in `Agreement.lean`**: `step_ofExit_pass_setInterruptible` and its
  success and failure helpers take the flag as an argument, and every current use passes `true`. They
  need nothing from stage 4's forms, and `Agreement.lean` rebuilds here anyway.
- Then build once: `lake build Effect4 Effect4.Laws`. Then `make gen-lcnf`, the `dune build`, and the
  gates stage 0a reaches: `make check-compiler check-native check-ocaml check-truth check-host-protocol`.
  The prep receipt gives each gate's baseline at the base commit, so a failure is yours or the
  baseline's.
- Commit stage 0a's files and stage 1's files separately. `Agreement.lean` holds both stage 0a's
  `suspendBodyAt_call` and the flag-general lemmas, so commit those two parts of it together.
- **Stop after slice A** and report. The coordinator reviews the core edit before the proof slices.

### Slice B: stage 0's proofs, the moves and the deletions

- Prove stage 0's goals: conservativity by structural induction, monotonicity in the package's
  `Approx`, unfolding, `denoteBlockB_of_asExit`, the one-step laws.
- Move the consumers: `denoteBody_getBody` and its user (`Ref/Cache.lean`); `CachedListAfterAdd` and
  `cached_list_after_add` (`Test/Dogfood/Scenario/Todo/Cached.lean`); `Test/Program/BlockMeaning.lean`;
  the two registry pointers.
- Delete what the plan's stage 0 lists, `mapOps` and `blockOf?` moved first. The `Mrec` import in
  `src/Effect4/Laws.lean` goes too; that is the one removal at a root, so name it in your receipt.
- No behaviour gate is reached. Regenerate the semantics report.

### Slice C: stage 1's block lemmas

- `bodiesOf_blockRows`, `PlainHooks.of_blockRows`, and its arms: `plainCode_compileEff` on `BodyRows`,
  the decided heads, `plain_at` through `Effs` spines and the root block. Write them in the leaf
  modules as theorems of their own, so `Machine.lean` is not edited again.

### Slice D: stage 2

- The two address lemmas, `compilesBlk`, `compilesBlk_root`. The outer induction is on the budget,
  the inner one structural, and the `Effs` helper recurses on the spine. Use the hop laws of §2.4 and
  the prefix laws of §2.1.

### Slice E: stage 3

- The closing steps (an exited run fixes a budget; stability), `h9_blocks`, and the two validated
  premises on blocks. `H9Blocks`'s coverage of the checker stays prospective until slice G.

### Slice F: stage 4

- Place stage 4's goals first, over the reworked forms.
- The context in the hosted spine: `localStepC` steps the context thunks and falls back to `localStep`;
  the hosted state and outcomes carry the context; `localStep` and `localRun` stay as they are.
- The machine forms take the context, with the cached budget equal to `budgetOf` of it.
- The steps: the five context thunks, the `restoreCtx` finalizer through `finalizerCode`, the one
  bracket lemma for `updateContextAt`, `service`, `Effect.context`.
- `PlainCode` and `PlainFrame` widen as the plan's stage 4 lists. That includes splitting
  `plainFrame_onExit` and `plainCode_onExit`, admitting `setInterruptible false` and admitting the
  yield wrapper frames.
- **The scheduler at every budget.** The segments read the fiber's own budget and `preventYield`.
  Settled positions relate to the local run up to the yield wrappers, by joinability. `Leads`,
  `Settled` and `Holds` are restated over it. `H9Blocks` stays receipt-conditioned. The plan's risk 6
  is the first thing to check: whether `meaning_settled` and `tape_holds_host` read `Leads` only
  through a final outcome.
- Generalize `ParamsAgree` and `CompilesBlk` over the context, and widen the fragment by the four
  constructs.
- No outside gate is reached, since no compile or machine definition changes. Run the whole axiom
  gate's module list for the hosted spine once at the end of the slice.
- **Stop after slice F** and report.

### Slice G: stage 5

- The twin builder: the service module's block, `main` invoking `<service>Context` and then the
  method. The checker's builder moves from `Todo.builtAt` to it.
- The keyed composite `list`, `list`, `add`, `list` (repository calls `all`, `insert`, `all`): its
  TypeScript side `cachedListAfterAdd` selected by `harness/truth/service/run-todo.ts`, and its Lean
  twin beside `listAddList` in `Test/Dogfood/Scenario/Todo/Cached.lean`.
- Gates: `make check-host-protocol`, and `check-target` and `check-ts-reader` if printed text
  changes.

## What you report

Your receipt opens with the one thing the coordinator must know before merging. Then, per slice:

- the base and head commits;
- the files changed;
- each command and its result, from the tool's own output;
- the `#axiom_audit` output;
- each goal's status (`#plan_status rows-block-host`);
- the open obligations;
- whether any evidence is bounded or host-only;
- any place the plan was wrong, with evidence.

Propose decisions rows in the receipt, never in the register.
