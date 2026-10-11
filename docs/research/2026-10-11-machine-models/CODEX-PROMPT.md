# Prompt for Codex: consolidate the goals lane on shared accounting laws

Work in the lean4-effect4 repository. Base: your integration branch, rebased on
`refactor/phase1-phase3` at the commit that adds this file or later. Read `AGENTS.md` first; it binds
you. Then read this folder's `README.md` and the earlier note
`../2026-10-11-machine-from-the-base/README.md`.

## The one thing to know first

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
3. **The ledgers as instances of L1.**
   - First delete what `LedgerFinalizer` makes redundant: `FinalizerCommands`' command proof and
     `FinalizerBookkeeping`'s edit lemmas, keeping their names as one-line instances.
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
6. **R1, R3, R7** (`README.md` §3).
   - Cut `Resume.continueWith`, `Dispatcher.armed`, `Pending.waitingOn`, the five dead
     `RaceAllState` fields and `Race.settled`. Make `finalizing` a `Bool`. `RaceAllState.initial_eq`
     is a frozen census law: propose its amendment in the receipt.
   - Read the yield budget from `budgetOf` and drop the fiber's copy.
   - Cut the scheduled wake branch, or record why it stays.
7. **L4 to L6** at any time: `AppendOnly` and `FreshSupply` for ids, keys and tokens; `Census` and
   `Linear` for the static site analyses. Reconcile `OncePlaced` with `Linear` in the receipt.

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
