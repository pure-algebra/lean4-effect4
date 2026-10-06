# 2026-10-06 brief for seat LIFT: the saved mask's chain at every live fiber of a run

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is the second slice of R11's open half, after seat MASKPOP.

## The slice

`saved_mask_pop_discipline` (`src/Effect4/Laws/Machine/MaskDiscipline.lean`) keeps the chain
`MaskChain` through the frame machine's pop and through each region's entry. It is a local
law. The open part of R11 is its lift: **each live fiber of a reached run holds the chain at
its start flag.** The first wrapper under a masked caller is its consumer, with Semaphore's
protected permit and Pool's `use`.

The receipt of seat MASKPOP maps the lift, in its item 8
(`docs/research/2026-10-06-seat-MASKPOP-receipt.md`). Its eight lines are this slice's plan.

## Read first

1. `AGENTS.md`, in full.
2. The receipt's item 8, its proposals P5 and P6, and its appendix (a scratch proof of line 6).
3. `src/Effect4/Laws/Machine/MaskDiscipline.lean`, whole.
4. Codex's report on the trap of the lift:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/deeper-proof-support/semantic/report.md`,
   and its correction of the condition:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-1336-qinv-pool-maskpop/maskpop/closing-addendum.md`.
   Codex's connector for the clearing, not compiled:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/dogfood-review-1406/lift/candidate.lean.txt`,
   with `review.md` beside it. It states that `RunFiber.cleared` keeps the chain exactly when
   the flag before the clearing is the base (`cleared_maskChain_iff`). Two commands clear a
   fiber: `Cmd.exitDone`, and `Cmd.finish` through `exitFiber.exitStore`. The condition must
   hold for both, and it must survive the observer commands and the nested work between a
   pending clear and its run. Carry it by `Guarded`.
5. `src/Effect4/Laws/Machine/Lift.lean`: `StepKeeps`, `Guarded`, `driveState_lift`,
   `stepDecisionState_lift`, `replayEval_lift`.
6. `src/Effect4/Machine/Fibers.lean`: `FiberCore.start`, `evaluatePrim`, `finishFrame`,
   `RunFiber.cleared`, `Cmd.exitDone`, `exitFiber`. `src/Effect4/Machine/Frames.lean`:
   `FrameFiber.step`.

## The assignment, in two parts

**Part A, the frames.** Two statements, each placed and proved in place:

1. `FrameFiber.step` keeps the chain at the same base (item 8, line 2). Every frame that
   `step` pushes is neutral.
2. A pop that answers nothing ends at an empty stack and at the base (line 6). The appendix
   holds a proof that the kernel accepted in scratch.

**Part B, the machine.** One invariant over the machine's fibers, and its lift:

3. State the invariant: each live fiber holds the chain at its base, the flag that
   `FiberCore.start` gave it (line 1).
4. State its command condition (line 5, as Codex corrected it): just before a command clears
   a fiber, that fiber's stack is empty, or its flag is its base. Emptiness after the
   clearing protects nothing: `RunFiber.cleared` empties the stack and keeps the flag.
5. Prove that each command keeps the invariant under the condition, and lift it through
   `Machine.Lift` (line 8). Use the existing `StepKeeps` and `Guarded` interface. Write no
   second run framework.
6. Show that the driver's own commands meet the condition where line 6 gives it: a finished
   frame has an empty stack.

**Write a design note first** (`docs/research/2026-10-06-seat-LIFT-design.md`): each statement
as Lean elaborates it, the invariant's exact form, and where the base of a fiber is stored or
recovered. Send its path, and go on. **Stop rule:** part A is the floor. If part B's
condition cannot be discharged for the driver's commands in its step, leave that statement a
planned goal, with the exact missing fact, and hand back.

**Not in this slice:** the bracket of a region (line 7: the body's run returns to the entry's
stack), any wrapper, any module, any budget or delivery law. `Program.MaskInv` stays as it is.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| Part A's two statements | `scope-lifetime-finalization`; R11, steps of the open part "the lift of saved-mask-pop-discipline to runs" | the polymorphic frame machine, one fixed base | nothing of a run | part B |
| Part B's invariant and its lift | the same; the lift itself | every reached machine under the command condition | the bracket of a region; a completed exit's flag beyond the chain; cleanup, delivery, liveness | the bracket's law, then the waiting wrapper under a masked caller |

## The files, and the rules

- New files: `src/Effect4/Laws/Machine/MaskRuns.lean` and `Test/Machine/MaskRuns.lean`. Root
  anchors: after `import Effect4.Laws.Machine.MaskDiscipline` in `src/Effect4/Laws.lean`, and
  after `import Test.Machine.MaskDiscipline` in `Test/All.lean`.
- You may add a statement to `MaskDiscipline.lean` when it is a step of that module's law.
  Do not edit a file under `src/Effect4/Machine/`: a comment there rebuilds most of the tree.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
- The shell's rules are in the dispatch message.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
- Controls in the battery: the sweep's states for part A; for part B, one constructed machine
  where an arbitrary `exitDone` breaks the chain (the trap), and the same machine under the
  condition.

## Acceptance

1. Part A's statements are theorems at `[propext, Quot.sound]`. Part B's are theorems, or
   each open one is a planned goal that the receipt lists first with its missing fact.
2. The controls pass, with the trap red without the condition.
3. Narrow builds after each step; the default `lake build` once at the end, with the gate
   lines; `make check-docs`.
4. Not run, and listed so: `make check-gen`, `check-slow`, `check-corpus`, `check-target`,
   `check-truth`, the conservativity script, `make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-LIFT-receipt.md`, short, in the handoff form of `AGENTS.md`:
the one thing to know before merging; base, head and commits; changed files; commands with
results; the statements as compiled, with axioms and `#plan_status`; what the bracket's law
still owes; the proposed registry text. One paragraph accounts for R1 to R13. Your last
message gives the head, the receipt's path and its first item.
