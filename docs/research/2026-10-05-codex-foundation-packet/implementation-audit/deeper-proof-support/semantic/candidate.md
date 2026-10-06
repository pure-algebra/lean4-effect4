# Proposed independent slice: the saved-mask discipline through a stack pop

Status: proposed statements, not Lean-checked. No repository declaration or goal is added.
Freeze: main `818a73ce`; PUB starts at `b199c15f` and owns Waiting and Queue operations.

## Placement before proof work

| Field | Proposed placement |
| --- | --- |
| Concept | `scope-lifetime-finalization` |
| Required property | R11's open run-level half of `saved-mask-restoration` |
| Claim | Proposed helper claim `saved-mask-pop-discipline`; preserve the existing boundary claim and its pointer |
| Consumer | A later machine-preservation instance for the saved-mask bracket, then Waiting under a masked caller and Semaphore's protected permit |
| Observation | The current interruptibility bit and the sequence of saved-mask frames, with one fixed base bit |
| Domain | Existing polymorphic `FrameFiber`, every stack, demand, skip flag and carried cause satisfying the stated stack relation |
| Premise | A fixed base bit and a well-formed mask chain; the internal pop helper also requires an empty detached scratch stack |
| Exclusions | No arbitrary-body run law, completed-exit law, delivery, registration, cleanup completion, liveness, host or printed-form agreement |
| Prerequisite | Coordinator records the helper placement and allocates disjoint Laws/Test files; then compile exact proposed statements and controls |

The predicate is proof data over the existing stack. It adds no field, instruction, program representation or runtime state.

## Statement shape

The notation below uses the current `Prim` and `FrameFiber` parameters. It is a declaration sketch, without proof bodies.
The Boolean relation can instead use the filed probe's projection and alternation if that is the cleaner implementation.
Keep one definition; do not maintain both as independent authorities.

```lean
-- Proposed predicate, not compiled.
def MaskChain (base : Bool) : Bool → List (Prim ν σ β ε δ ι α) → Prop
  | flag, [] => flag = base
  | flag, Prim.setInterruptible saved :: rest =>
      flag = !saved ∧ MaskChain base saved rest
  | flag, _ :: rest => MaskChain base flag rest
```

The first helper's empty scratch premise matches `getCont`'s actual call to `popFrom`.
An induction with an arbitrary scratch stack would need a stronger relation describing its position.
Do not silently remove this premise.

```lean
-- Proposed main induction helper, not compiled.
popFrom_maskChain
    (base : Bool) (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α))
    (f : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α))
    (scratchEmpty : f.stack = [])
    (valid : MaskChain base f.interruptible frames) :
  MaskChain base (FrameFiber.popFrom demand skip frames f cause).fiber.interruptible
    (FrameFiber.popFrom demand skip frames f cause).fiber.stack

-- Proposed public helper, not compiled.
getCont_maskChain
    (base : Bool) (f : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α))
    (valid : MaskChain base f.interruptible f.stack) :
  MaskChain base (f.getCont demand skip cause).fiber.interruptible
    (f.getCont demand skip cause).fiber.stack

-- Proposed adapter to the machine's actual finished-frame path, not compiled.
frameExitState_maskChain
    (base : Bool) (f : FrameFiber ν σ β ε δ ι α)
    (valid : MaskChain base f.interruptible f.stack) :
  MaskChain base (Machine.frameExitState f).interruptible
    (Machine.frameExitState f).stack
```

The declarations require the same decidable-equality parameters as the existing pop definitions.
The proof must keep the project ceiling `[propext, Quot.sound]`.
The exact namespace and implicit parameters need elaboration; these snippets are not compiled signatures.

Two small corollaries make the consumer connection explicit:

- Entry through `uninterruptible` or `interruptibleRegion` keeps `MaskChain` at the same base.
- Two states with the same base and the same stack have the same current bit.

The second corollary alone does not show that a body's run returns to the relevant stack.
That connection remains a separate machine/run obligation.

## Reuse route

1. Reuse `uninterruptible_masks`, `uninterruptible_already_masked`, `interruptibleRegion_masked`, and `interruptibleRegion_already` for entries.
2. Reuse `Prim.ensure_setInterruptible_flag` and `Prim.ensure_setInterruptible_stack` for a restoring frame.
3. Use `FrameFiber.ensure_stack_cases` for the only hooks that push a new restoring frame.
4. Use `passPushed_nil`, `passPushed_fiber`, and the existing restoring-frame equations for that push.
5. Follow `popFrom_interruptedCause`'s existing structural induction shape: `continueFrom_cases`, `popFrom_continue_fiber`, and `popFrom_answer_fiber`.
6. Use `popFrom_fiber_cause` to avoid a duplicate proof for carried causes.
7. Split `getCont` once on its deferred-interrupt branch. That branch changes no stack or current bit.
8. Unfold only the two branches of `Machine.frameExitState` for the adapter.

All these declarations are in `src/Effect4/Machine/Frames.lean`, except `Machine.frameExitState` in `src/Effect4/Machine/Fibers.lean`.
The established boundary packaging remains in `src/Effect4/Laws/Program/Typed/Mask.lean`.
A new lower law module should reuse the lower equations rather than import the higher typed-program module.

## Proposed positive and red controls

These are source-derived control sketches, not executed outcomes.

| Control | Required observation |
| --- | --- |
| Both empty stacks, each with its own matching base | Entry and pop leave that bit and empty stack |
| `flag=false`, stack `[setInterruptible true]`, base `true` | A completed pop returns `flag=true`, empty stack |
| Nested valid chain with both saved bits, with neutral frames interleaved | The result satisfies the same base-indexed relation |
| A cause pending when `setInterruptible true` passes | The bit is restored; the existing replacement is still failure with that cause |
| `onExit` or `asyncFinalizer` masks and pushes during the pop | The pushed frame is visited through the existing live-stack path |
| Mutant drops a restoring frame without applying its hook | The one-frame case above breaks the base relation |
| Mutant masks for a finalizer without pushing its restore | A true-base positive becomes a false-bit empty stack and fails |
| Remove the fixed-base premise from the same-stack corollary | Two empty stacks with opposite bits refute the claim |
| Keep a base but omit alternation | Two opposite bits over the same `[setInterruptible true]` stack have the same bottom bit |

Keep `popFrom_asyncFinalizer_pops_its_push` as the already-proved control for visitation and pending-cause order.
A mask-chain invariant alone does not prove that order or that the finalizer runs exactly once.

## Independent files and acceptance boundary

Proposed ownership: new `src/Effect4/Laws/Machine/MaskDiscipline.lean` and `Test/Machine/MaskDiscipline.lean`.
The coordinator owns root imports and registry joins.
This slice edits no PUB, Queue step, REFS, authoring, printer, host or generated file.

Its receipt must retain the exact statements, positive/red outputs, transitive axioms and narrow builds.
It must say that the whole-run mask invariant remains open.
No implementation or proof checking occurs in this research task.
