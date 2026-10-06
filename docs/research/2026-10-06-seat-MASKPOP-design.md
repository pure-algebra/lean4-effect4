# 2026-10-06 seat MASKPOP design: the saved mask's chain is kept through a pop of the stack

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-maskpop-brief.md`. Base: `6b2b5cda`. A scratch
probe at the base states and proves every statement below, at `[propext, Quot.sound]`. No file
of the slice is in the tree yet, so this note claims no theorem.

## 1. The predicate

Codex's sketch elaborates unchanged, in `namespace Effect4.FrameFiber`. Lean reads it as a
structural recursion on the stack. Its seven alphabets are implicit, and it takes no instance.

```lean
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
def MaskChain (base : Bool) : Bool → List (Prim ν σ β ε δ ι α) → Prop
  | flag, [] => flag = base
  | flag, Prim.setInterruptible saved :: rest => flag = !saved ∧ MaskChain base saved rest
  | flag, _ :: rest => MaskChain base flag rest
instance MaskChain.decidable (base : Bool) :
    ∀ (flag : Bool) (stack : List (Prim ν σ β ε δ ι α)), Decidable (MaskChain base flag stack)
```

## 2. The statements

Each binder list is explicit and in this order. The types are those of the pop's definitions.

| Name | Namespace; instances | Premises | Conclusion |
| --- | --- | --- | --- |
| `MaskChain.flag_eq` | `Effect4.FrameFiber`; none | `MaskChain base flag stack`, `MaskChain base flag' stack` | `flag = flag'` |
| `ensure_maskChain base frame fiber rest` | the same | `MaskChain base fiber.interruptible (frame :: (fiber.stack ++ rest))` | the chain over `(frame.ensure fiber).fst`'s flag and its stack `++ rest` |
| `uninterruptible_maskChain base f`, `interruptibleRegion_maskChain base f` | the same | `MaskChain base f.interruptible f.stack` | the chain over `f.uninterruptible`, and over `f.interruptibleRegion.fst` |
| `passPushed_maskChain base demand skip fiber cause rest` | `Effect4.FrameFiber`; `[DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]` | `MaskChain base fiber.interruptible (fiber.stack ++ rest)` | the chain over the drain's fiber: its flag and its stack `++ rest` |
| `passPushed_ensure_stack_nil demand skip frame fiber cause` | the same | `fiber.stack = []` | `(passPushed demand skip (frame.ensure fiber).fst cause).fiber.stack = []` |
| `popFrom_maskChain base demand skip frames f cause` | the same | `f.stack = []`, `MaskChain base f.interruptible frames` | the chain over the flag and the stack of `(popFrom demand skip frames f cause).fiber` |
| `getCont_maskChain base f demand skip cause` | the same | `MaskChain base f.interruptible f.stack` | the chain over `(f.getCont demand skip cause).fiber` |
| `frameExitState_maskChain base f` | `Effect4.Machine`; the same four | the same | the chain over `Machine.frameExitState f` |

The placed theorem holds six fields: `pop`, `getCont`, `frameExit`, `uninterruptible`,
`interruptibleRegion` and `sameFlag`. The first five are the rows above. `sameFlag` reads two
fibers with one base and equal stacks: the chain for each gives equal flags.

```lean
structure MaskPopDiscipline (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] : Prop
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem saved_mask_pop_discipline (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    MaskPopDiscipline ν σ β ε δ ι α
```

It lands first as a `proof_goal`, in `namespace Effect4.Machine`. The structure is not clumsy:
its alphabets are explicit parameters, and `#plan_status` reads the goal with them.

## 3. The induction

`popFrom_maskChain` rewrites the carried cause away (`popFrom_fiber_cause`). Then it is an
induction on `frames`, with the fiber general, in the form of `popFrom_interruptedCause`.

| Case | What closes it |
| --- | --- |
| `[]` | `popFrom_nil`; the scratch premise turns the fiber's stack into `[]` |
| the head answers | `popFrom_answer_fiber`; then `ensure_maskChain` at the empty scratch |
| the head passes, or the skip discards its answer | `popFrom_continue_fiber`; then the two shapes of `continueFrom_cases` |
| shape 1: the drain did not answer | the induction hypothesis, at `passPushed_ensure_stack_nil` and `passPushed_maskChain` |
| shape 2: the drained frame answered | `passPushed_maskChain`, whose conclusion is the goal |

`ensure_maskChain` splits the hook by `cases frame`, with one catch-all for the neutral hooks.

- **A restoring frame:** its two own equations, `Prim.ensure_setInterruptible_flag` and
  `Prim.ensure_setInterruptible_stack`.
- **`onExit`:** `Prim.ensure_onExit_masks`, `Prim.ensure_onExit_told_not_to` and
  `Prim.ensure_onExit_already_masked`.
- **`asyncFinalizer`:** `Prim.ensure_asyncFinalizer_masks` and
  `Prim.ensure_asyncFinalizer_already_masked`.

The other steps use these existing lemmas, all of `src/Effect4/Machine/Frames.lean`.

| Step | Uses |
| --- | --- |
| `passPushed_maskChain` | `passPushed_fiber_cause`, `passPushed_nil`, `passPushed_fiber` |
| `passPushed_ensure_stack_nil` | `ensure_stack_cases`, `passPushed_nil`, `passPushed_fiber`, `Prim.ensure_setInterruptible_stack` |
| `getCont_maskChain` | one `split` of `getCont` on its branch of a deferred interrupt |
| `frameExitState_maskChain` | the two branches of `Machine.frameExitState` (`src/Effect4/Machine/Fibers.lean`) |
| the two entries | `uninterruptible_masks`, `uninterruptible_already_masked`, `interruptibleRegion_masked`, `interruptibleRegion_already`, by `aesop` |

## 4. Each difference from Codex's statements

Codex's three statements and its predicate are true as written, and each elaborates.

- **Namespaces and instances.** Section 2 fixes them. Codex left both open.
- **Two general steps.** `ensure_maskChain` and `passPushed_maskChain` ask no scratch premise:
  the popped frame sits on top of the scratch stack. Codex names no such step.
- **One equation of the frames is missing.** `passPushed_ensure_stack_nil` says that one drain
  empties what one hook pushed. The receipt proposes its move to `Frames.lean`.
- **`ensure_stack_cases` serves the stack only.** It gives no flag where the stack is
  unchanged. So the flag comes from the hooks' own equations.
- **A `Decidable` instance.** It decides the one definition, so the battery evaluates the
  chain on real fibers. It is no second definition.
- **The same-flag corollary** is `MaskChain.flag_eq` on two flags, and `sameFlag` on two fibers.

## 5. The controls, and what the slice does not establish

The battery holds the brief's five positive rows and five red controls on `Prim` at `Nat`. It
adds one sweep: every stack of at most four frames over eight frames.

The probe shows a second witness for the scratch premise. A chain over the scratch stack
followed by the frames does not replace it. At flag false, scratch `[setInterruptible true]`,
frames `[setInterruptible false]` and base false, the pop ends at flag true with an empty stack.

The slice states no law of a run, no bracket of a region and no base of a fiber in a run.
`Cmd.exitDone` clears a stack and keeps its flag, so the later lift keeps a condition on the
pending commands.

## 6. Addendum, at the landing (2026-10-06)

The landed tree has every statement of section 2, with its name, its namespace and its binders.
It differs from this note in two places of the proofs. The receipt
(`docs/research/2026-10-06-seat-MASKPOP-receipt.md`) holds the commands and their results.

- **The entry of the `interruptible` region** also reads `setFiberInterruptible_flag` and
  `setFiberInterruptible_pushes`, the two equations of the function that it calls.
- **`MaskChain.decidable` splits the frame by `cases`**, inside the structural recursion. In a
  catch-all arm of a plain `match` the frame is a variable, and the chain does not reduce there.
