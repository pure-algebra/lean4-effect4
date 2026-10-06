# 2026-10-06 seat LIFT design: the saved mask's chain at every live fiber of a run

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-lift-brief.md`. Base: `f3568844`. No file of
the slice is in the tree yet, so this note claims no theorem. Each statement below is in a
scratch probe at the base. Section 9 lists what each probe shows.

A fiber is "live" in this note when it has not exited: its field `exit` is `none`.

## 1. Part A: the frames

The statements are in `namespace Effect4.FrameFiber`, but for the last two, which are in
`namespace Effect4.Machine`. Each takes the four instances of the pop's definitions,
`[DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]`, but for the first.

| Name | Premises | Conclusion |
| --- | --- | --- |
| `MaskChain.base_eq` | `MaskChain base flag stack`, `MaskChain base' flag stack` | `base = base'` |
| `armA_maskChain interp frame value provided next pushed` | `frame.armA interp value provided = some (next, pushed)`, `MaskChain base flag rest` | `MaskChain base flag (pushed ++ rest)` |
| `armE_pushes_nothing interp frame cause provided next pushed` | `frame.armE interp cause provided = some (next, pushed)` | `pushed = []` |
| `step_maskChain base interp f` | `MaskChain base f.interruptible f.stack`, `(f.step interp).fst = FrameStep.running next` | `MaskChain base next.interruptible next.stack` |
| `popFrom_unanswered_stack demand skip frames f` | `f.stack = []`, `(popFrom demand skip frames f).answer = ContAnswer.empty` | `(popFrom demand skip frames f).fiber.stack = []` |
| `popFrom_unanswered_flag base demand skip frames f` | the same two, and `MaskChain base f.interruptible frames` | `(popFrom demand skip frames f).fiber.interruptible = base` |
| `getCont_unanswered_stack f demand skip cause` | `(f.getCont demand skip cause).answer = ContAnswer.empty` | `(f.getCont demand skip cause).fiber.stack = []` |
| `getCont_unanswered_flag base f demand skip cause` | the same, and `MaskChain base f.interruptible f.stack` | `(f.getCont demand skip cause).fiber.interruptible = base` |
| `step_finished_stack interp f exit` | `(f.step interp).fst = FrameStep.finished exit` | `(frameExitState f).stack = []` |
| `step_finished_flag base interp f exit` | the same, and `MaskChain base f.interruptible f.stack` | `(frameExitState f).interruptible = base` |

The brief's two statements are `step_maskChain` and the pair `popFrom_unanswered_stack`,
`popFrom_unanswered_flag`. The pair is the receipt's appendix, renamed: its word "empty" also
reads as a pop of an empty stack, which is `popFrom_nil`.

`step_maskChain` reads the step by its two resumptions. A value arm pushes `whileLoop` or
`iterator` (`armA_maskChain`), and a cause arm pushes nothing (`armE_pushes_nothing`). Each
other equation of `FrameFiber.step` pushes the primitive that it reads, or it writes `current`.
None pushes a restoring frame.

`step_finished_stack` needs one more fact than the pop's. `resumeValue` also finishes where an
answering frame has no value arm. `getCont_answer_hasArm` and `Prim.armA_isSome`
(`src/Effect4/Machine/Frames.lean`) refuse that case, and `Prim.armE_isSome` refuses it for a
cause.

## 2. Where a fiber's base is stored

The machine stores no base. `RunFiber.make` hands the flag to `FiberCore.start`
(`src/Effect4/Machine/Fibers.lean`). No field of the fiber, no fork record and no event keeps it
(reading). After a fiber's first region the flag alone does not show the base.

So the base is proof data, and it is the world of the lift. `Machine.Lift`
(`src/Effect4/Laws/Machine/Lift.lean`) takes a world type `W` with an order.

- **The world** is a table of start flags, `List Bool`. Entry `n` is the flag that the fiber
  with id `n` started with.
- **The order** is the prefix order. A spawn appends one entry, and no command changes an entry.
- **The length** of the table is the machine's `nextId`. So the next spawn's entry lands at the
  child's id.

```lean
def basesOrder : WorldOrder (List Bool) :=
  ⟨fun bases bases' => bases <+: bases', List.prefix_refl, List.IsPrefix.trans⟩
```

A fiber's entry never changes, so two reached machines of one run read one base for one fiber.
That is what the bracket's law needs for `sameFlag`.

## 3. The invariant's exact form

```lean
def MaskKept (bases : List Bool) (f : RunFiber ν σ β ε δ ι α χ) : Prop :=
  ∃ base, bases[f.id.value]? = some base ∧
    (f.exit = none → MaskChain base f.frame.interruptible f.frame.stack)

def MaskRuns (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  bases.length = m.nextId ∧ ∀ f ∈ m.fibers, MaskKept bases f
```

Each fiber of the table has its entry. A live fiber holds the chain at its entry. The
invariant is over the concrete frame instance: `MaskChain` reads a `FrameFiber`.

## 4. A finding: the chain fails at an exited fiber of a reached machine

The brief's condition protects an invariant over every fiber of the table. That invariant is
false at a reached machine (reproduced: a finite probe on one tape, in scratch).

| Item | Value |
| --- | --- |
| Interpreter | a toy `RunInterp` at the alphabets `Nat`; its `parkOf` reads one thunk as the registration of race 0 |
| Programs | fiber 0 forks fiber 1, then hosts race 0; fiber 1 awaits fiber 0, then evaluates that registration |
| Tape | `[.evaluate ⟨0⟩, .fire ⟨0⟩]`, at fuel 400 |
| Reached machine | not stuck; fiber 0 has exited, with flag false and an empty stack |
| Fiber 0's start flag | true |

The cause is two rules of the driver, both read in `driveStep`.

1. `Cmd.registrationDone` continues the race's host, whichever fiber evaluated the registration.
2. `Cmd.loop` steps a fiber that has exited.

So fiber 1 steps fiber 0 between fiber 0's publication and its `Cmd.exitDone`. Fiber 0 enters a
masked region and parks there. Then `Cmd.exitDone` clears its stack and keeps its flag.

The probe's interpreter is outside the admitted construction image: there, only a race's host
evaluates its registration. `Machine.Lift` ranges over every interpreter, so the lift must not
assume that image.

**The choice.** The invariant ranges over the live fibers. It holds at the probe's reached
machine. Its consumer, the bracket's law, reads a fiber between its start and its exit. The
completed exit has its own statement, at its event (section 7).

## 5. The command condition

Two commands clear a fiber. `Cmd.exitDone` runs `RunFiber.cleared`. `Cmd.finish` runs it
through `exitFiber.exitStore`, after `RunFiber.publish` in the same step. So `Cmd.finish` clears
a fiber that has exited, and the invariant asks nothing of it. The condition is on
`Cmd.exitDone` alone.

```lean
def ClearReady (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) :
    Cmd ν σ β ε δ ι α → Prop
  | Cmd.exitDone id => ∀ f, m.fiber? id = some f →
      f.exit.isSome = true ∨ f.frame.stack = [] ∨ bases[id.value]? = some f.frame.interruptible
  | _ => True
```

The last two alternatives are the brief's: the stack is empty, or the flag is the base. The
first is new: the fiber has exited. The condition reads the machine just before the clearing.

The condition on the pending commands is the first alternative, since no command resets `exit`.

```lean
def Exited (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) : Prop :=
  id.value < m.nextId ∧ ∀ f ∈ m.fibers, f.id = id → f.exit.isSome = true

def ClearsExited (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) : Prop :=
  ∀ id, Cmd.exitDone id ∈ cmds → Exited m id
```

`Lift.Guarded` carries it as its fact `I` on the pending commands. The machine fact `J` is
`MaskRuns`, and the snapshot fact `O` is `True`.

The driver meets it (reading, to be proved in the step). `exitFiber.exitStore` issues
`Cmd.exitDone` for the fiber that it has published. The bound `id.value < m.nextId` keeps a
later spawn from taking the id.

## 6. The statements of part B

Lean elaborates each one. Each takes the four instances.

```lean
theorem driveStep_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α))
    (kept : MaskRuns bases m) (ready : ClearReady bases m c) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveStep interp m c rest).1

theorem maskRuns_stepKeeps (interp : RunInterp ν σ β ε δ ι α χ St)
    (ts : List (Machine.Task ν σ β ε δ ι α)) :
    Lift.StepKeeps basesOrder interp
      (Lift.Guarded (fun bases m => MaskRuns bases m) (fun _ m cmds => ClearsExited m cmds)
        (fun _ _ _ => True) ts)

theorem maskRuns_decisionLift (interp : RunInterp ν σ β ε δ ι α χ St) :
    Lift.DecisionLift basesOrder interp (fun bases m => MaskRuns bases m)
      (fun _ m cmds => ClearsExited m cmds) (fun _ _ _ => True) (fun _ _ _ => True)

theorem replayEval_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (kept : MaskRuns bases m) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replayEval interp fuel tape m).machine
```

| Statement | The brief's item | What it is |
| --- | --- | --- |
| `driveStep_maskRuns` | 5 | each command keeps the invariant under the condition |
| `maskRuns_stepKeeps` | 5, 6 | the same through `Guarded`: the driver's own commands keep the pending condition |
| `maskRuns_decisionLift` | 5 | each edit that a decision makes outside the command loop |
| `replayEval_maskRuns` | 5 | the placed theorem: each reached machine, by `stepDecisionState_lift` and `replayEval_lift` |

Two statements give the start. The empty machine holds the invariant at the empty table. A root
that `RunFiber.make` appends at flag `flag` extends the table by `flag`. A spawn has the same
form, and its entry is the flag that `FiberCore.start` gave the child.

The lift asks no admission of a decision: its fact `A` is `True`.

## 7. Line 6 at the machine: a finished frame

`Outcome.finished` comes from `evaluatePrim.finishFrame` alone, after `frameExitState`
(reading). So the driver issues `Cmd.finish` at an empty stack.

```lean
theorem evaluatePrim_finished_stack (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool)
    (exit : Exit β ε δ ι α) (finished : (evaluatePrim interp m f y).outcome = Outcome.finished exit) :
    (evaluatePrim interp m f y).fiber.frame.stack = []
```

A second statement gives the flag: with the chain over `f`, the finished fiber's flag is the
base. Both are the completed exit's statement, at its event. The invariant over live fibers
does not need them. They are what the brief's item 6 asks for `Cmd.finish`.

They give no state invariant of an exited fiber. Section 4 shows why: a later command steps an
exited fiber.

## 8. The proof

The step's proof reads each fiber through one relation, and each machine through a second.

```lean
/-- `g` is a later state of the fiber `f`. -/
def Later (f g : RunFiber ν σ β ε δ ι α χ) : Prop :=
  g.id = f.id ∧ (g.exit = none → f.exit = none) ∧
    (g.exit = none → ∀ base, MaskChain base f.frame.interruptible f.frame.stack →
      MaskChain base g.frame.interruptible g.frame.stack)

/-- `m'` is a later state of the machine `m`. -/
def Aged (m m' : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  m.nextId ≤ m'.nextId ∧ ∃ born : Nat → Bool, ∀ g ∈ m'.fibers,
    (∃ f ∈ m.fibers, Later f g) ∨
      (m.nextId ≤ g.id.value ∧ g.id.value < m'.nextId ∧
        (g.exit = none → MaskChain (born g.id.value) g.frame.interruptible g.frame.stack))
```

- **Both are preorders.** Each helper of the driver gets one statement, and a command composes
  them.
- **Both read projections only.** A write of another field is closed by reflexivity, since the
  projections reduce. The probe closes two arms of `evaluatePrim` this way.
- **`MaskRuns` and `Exited` follow `Aged`.** `Aged` gives the new table from `born`. So one
  pass over the commands serves the machine fact and the pending fact.
- **`Cmd.exitDone` is the one command outside `Aged`.** Its case reads `ClearReady`.
- **One statement per evaluation** holds four facts of an `Iter`. The machine has aged, and
  the fiber is later. No nested command clears, and a finished outcome has an empty stack.

The frame steps come from part A and from `saved_mask_pop_discipline`
(`src/Effect4/Laws/Machine/MaskDiscipline.lean`). The fiber machine's own pushes are
`asyncFinalizer` and `iterator`, both neutral.

Each proof takes no `first`, no `try` and no `simp_all`. The module registers no rule in a bank.

## 9. Codex's connector, and the probes

Codex's `cleared_maskChain_iff` elaborates as written, and `rfl` proves it (tested: scratch,
axioms `[propext]`). It is the case of `Cmd.exitDone` under the brief's two alternatives.

| Probe (scratch) | Result | Evidence |
| --- | --- | --- |
| `partA3.lean` | each statement of section 1 is proved, at `[propext, Quot.sound]`, with warnings as errors | tested |
| `partB2.lean` | each definition and statement of sections 2 to 7 elaborates; the bodies are not proved | tested |
| `partB1.lean` | `Later`, `Aged` and their reflexivity; two arms of `evaluatePrim` close by reflexivity | tested |
| `hijack1.lean` | section 4's reached machine | reproduced: a finite probe |
| `codex1.lean` | Codex's connector, unchanged | tested |

## 10. The controls, and what the slice does not establish

The battery evaluates the invariant on machines at the alphabets `Nat`.

- **The trap:** one live fiber at flag false under `[setInterruptible true]`, at base true. An
  arbitrary `Cmd.exitDone` breaks the invariant there.
- **The same machine under the condition:** once with the fiber published, once at an empty
  stack, once at its base. Each keeps the invariant.
- **The reached machine of section 4:** the invariant over live fibers holds, and the form over
  every fiber is red.
- **Part A:** the sweep's states through `FrameFiber.step`, and each unanswered pop.

The slice states no bracket of a region, no wrapper and no module law. It gives no cleanup, no
delivery, no budget and no liveness. It gives no flag of an exited fiber as a state invariant.
An invariant is not progress.

**The stop rule.** Part A is proved in scratch. Part B's statements are not proved yet. If the
step's proof fails at a command, that statement lands as a planned goal with its missing fact.
