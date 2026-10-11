# Prompt for Codex: the machine's base laws, and the cleanup they allow

Work in the lean4-effect4 repository, branch `refactor/phase1-phase3`, from commit `87d117009` or
later. Read `AGENTS.md` first; it binds you. Then read this folder's `README.md` (the machine from
its base) and `context-transformers.md` (the dynamic context). This lane runs beside the goals
packet's lane. Do not reorder that lane; take this one when it has room.

## What already landed (verify, do not trust)

- `src/Effect4/Laws/Program/Moves.lean`: one native evaluation edits the evaluated fiber's frame
  part by a word of eight moves (`FrameMove`, `Moves`): answer, push a park's cancel frame, a frame
  step that goes on, one that finishes, a pop, the mask, the unmask, the loop's pending failure.
  Proved at every level: `evaluatePrim_moves`, `withFiber_moves`, `exitScoped_moves`,
  `evaluateNative_moves`, `iteration_moves`. The induction is `Moves.keeps`.
- `src/Effect4/Laws/Program/MovesConnect.lean`: connectors. The guard's `interruptedCause` and
  `deferredCause` chains, and the evaluation half of `MaskRuns` (`evaluateNative_maskChain`), are
  each one fact per move plus `Moves.keeps`.
- `src/Effect4/Laws/Program/Footprint.lean`: one evaluation's footprint on the run fiber
  (`Footprint`): the frame moves, and the id, exit, running bit, finalizing exit, own observers
  and children are kept. Connectors: `iteration_id`, `iteration_exit`, `iteration_running`.
- `src/Effect4/Laws/Program/Interference.lean`: after one evaluation or iteration, every fiber of
  the machine is an old fiber (same id) under a word of three listed edits (an observer appended,
  observers filtered, an interrupt recorded), or a new one (`Interferes`, `iteration_interferes`).
  No edit changes another fiber's id or exit (`OtherEdits.id`, `OtherEdits.exit`).
- `src/Effect4/Laws/Machine/StackLocal.lean` and `src/Effect4/Laws/Program/StackLocal.lean`: the
  fiber machine's frame rule at one evaluation. A frame-machine step that goes on is the same over
  more frames, events included (`step_under_pair`). A native iteration that does not finish
  (`GoesOn`) is the same over more frames, with the same machine (`iteration_under`, down through
  every level and all 24 actions).
- `src/Effect4/Laws/Program/CommandFrames.lean`: after any command of the native loop, every fiber
  is an old fiber (same id) whose frame moved by a word of frame edits, or a new one
  (`driveStep_framesFollow`). The edits: an evaluation's moves, an interrupt recorded, the deferred
  bit set, the stack cleared, the parallel close's iterator pushed.
- `Test/Counterexamples/Program/ContextReset.lean` (`E4-CTX-CE-001`) and
  `Test/Counterexamples/Codegen/PrintDistributes.lean` (`E4-PRINT-CE-001`), both seeded.

All seven modules audit within `[propext, Quot.sound]` (`probes/AuditMoves.lean`, 706 declarations).

## The work, in order

1. **The guard cleanup (C1).** About ten invariants each re-prove their preservation by their own
   case analysis over the same evaluator arms (README §4). The guard bundle
   (`src/Effect4/Laws/Program/Guard/`, 14,321 lines) holds per-field chains through the evaluator's
   ten levels, written with `repeat' first | … | split` and `simp_all`.
   - Replace each chain's evaluator-level lemmas (`stepFrame_X`, `finalizerOr_X`, `withFiber_X`,
     `evaluatePrim_X`, `exitScoped_X`, `evaluateNative_X`, `iteration_X`) by the moves or the
     footprint. Keep each lemma's name and statement, so no consumer moves.
   - A chain over a field the footprint does not yet name: extend `Footprint` with the field, or
     add the field's per-move fact. A chain that reads the outcome (`ReadyOutcome`,
     `PendingShape`): extend the classification with the outcome first (C2).
   - `Guard/DeferredCause.lean` lines 23–75 repeat `Guard/Interruption.lean` lines 8–63; remove the
     copy and import the original.
   - Then `MaskRuns`'s evaluation half (`evaluatePrim_keepsMask`, `withFiber_keepsMask`) by
     `evaluateNative_maskChain`, and the other invariants of README §4 where the moves serve.
   - This rebuilds the law graph above the guard. Land it as one sweep, after the goals lane's
     current landing, not between its commits.
2. **The outcome and liveness (C2, base law B2).** The evaluation's half and the commands' frame
   half landed (`Interference.lean`, `CommandFrames.lean`). Refine `FramesFollow` so that a fiber
   whose exit is still `none` reached its frame by edits without `clearStack` (only an exited fiber
   is cleared); with it, `MaskRuns`'s command half is an instance (`move_maskChain` plus one fact
   per edit). Extend the classification to the outcome (parked exactly after a park move; finished
   exactly after a finish) and record what a spawned fiber starts as (its frame a compiled program,
   its context the parent's). This is Owicki and Gries's non-interference made one theorem
   (`MaskAged` is its mask instance). It is the generic half of the goals packet's G2, and the
   goals lane's per-program assertions can then cite it instead of re-deriving it.
3. **Stack locality along a run (B3's run half).** The evaluation's half landed
   (`iteration_under`). Next the commands that touch the fiber's frame (`deliver`, `resume`,
   `interruptTarget`, `afterInterrupt`, `closeParAwait`, and `settle`'s write-back), then the lift
   through `Machine.Lift`: until a pop reaches the entry's stack, the fiber's stack is its own
   frames over that stack. That discharges the premise `inside` of `compiled_region_bracket`
   (`src/Effect4/Laws/Program/MaskBracket.lean`). Consumers: Semaphore's protected permit and
   Pool's `use` (R11).
4. **Points well formed (B4, the goals packet's G1a)**, then **the stack is a path (B5)**: in each
   call segment the frames' nodes are a chain of proper prefixes, a segment opens at a call site,
   and a parameter's frames hang off its call site (the topology note's probe,
   `../2026-10-11-topology-graphs/probes/StackPaths.lean`).
5. **The services' chain (B6)** waits for the owner's ruling on the context note's option A. Do not
   start it before.

## How to work

- Place every obligation before you work it (AGENTS.md, Trust): concept, question, reach, limits,
  consumer. The README's §6 table gives each base law's placement.
- Compile first: state a structure as `proof_goal` with `@[semantics …]`, prove it by narrow
  builds, replace the goal in place.
- Write the case analysis arm by arm, as `Moves.lean` does: `split`, `cases`, `exact`. No
  `repeat' first`, `first`, `try` or `simp_all` in new or touched proofs. aesop did not apply the
  move constructors through the record projections (tested); a plain `exact` did.
- Narrow builds only (`LEAN_NUM_THREADS=3 lake build <Module>`), then `#axiom_audit` over the
  touched modules. The gates run at a sweep.
- Do not edit `docs/core/decisions.md` or `lakefile.toml`; propose rows in the receipt.

## Deliverable

A receipt, `docs/research/<date>-codex-base-laws-receipt.md`: first the one thing to know before
merging, then base and head, changed files, commands and results, the audit output, the open goals,
the deferred gates, and the line count the cleanup removed (`wc -l` before and after, per module).
Never push. Commit by explicit paths; `git add -f` for `docs/research`.
