import Effect4.Laws.Program.Typed.Stack
import Effect4.Laws.Machine.Lift
import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Program.Typed.Scheduler
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.Typing.CheckInversion

/-!
# Laws.Program.Typed.Assembly — the typed state of the reference machine, split at the cut

Slice 5's assembly, split by decisions row 134 (ruled 2026-10-01; the formal pass's G1 and its
verifier's split keyed on `running`). The generated predicate bundle `Preds` is instantiated once
(`preds`), independent of the machine and the queue: it types every stored value, exit, stack and
payload position. Current code is typed by two hand clauses keyed on the fiber's own flags and on
the queue, because whether a fiber's code is read again depends on them, not on the saved frame:

* `MachineTyped` (`J`, machine-only and cut-tolerant): world validity, the generated predicate
  with the correlations (`TypedState`), the code of every fiber that has not exited and is not
  running (`LiveCode`), and `stuck = none` with the liveness clauses of row 139 (`MachineLive`).
  A budget cut drops the residue (`Machine/Fibers.lean:2080`, `:2139-2140`) and leaves a running
  fiber whose code no queued command will read: `J` does not type it (`E4-TYPED-CE-011`,
  `Test/Counterexamples/Machine/Semantics/StaleCode.lean`).
* `ConfigTyped` (`I`, the configuration `(m, q)`): `J`, the code of each running fiber a queued
  `loop` or `deliver` reads (`ReadCode`), and the queue facts of rows 106 and 133 (`QueueOk`).

In H1's vocabulary: a running fiber that no queued `loop` or `deliver` continues is inert; `J`
reads that at the empty queue, `I` at the real queue. A halted machine is outside `J`
(`stuck = none`, row 139), which supersedes H1's halt extension of row 133 (plan O4).
`DecisionLift` is unchanged (`Laws/Machine/Lift.lean:308-355`): each command obligation is
`StepPreserves` over `I` at the dispatch premise `m.stuck = none`, and with the fire snapshot
riding as a suffix of the queue they are exactly the lift's `step` premise
(`guarded_stepKeeps_of_stepPreserves`). `decision_preserves` and `typedState_reachable` are
stated over `J`. No configuration capstone over `I` is declared: no consumer reads one (M7 reads
`J` through `obs`; the decision lift builds `I` from `J` at fresh queues).

The commands that continue a running fiber, and how `I` types it (the reference code-site census
H1 left open, `2026-09-30-seat-codex-slice6-evidence/after-addendum-6/H1/resolution/README.md`;
`Machine/Fibers.lean` at `bb269fde`):

| Command | Reads the fiber's current code? | Typing in `I` |
| --- | --- | --- |
| `loop id` | yes: `iteration` evaluates it (`:1857-1860`) | `ReadCode`: the code with its stack at `Γ id` |
| `deliver id` | yes: the evaluator pops the delivered value (`:1861-1864`) | `ReadCode` |
| `finish id ex` | no: `exitFiber` publishes `ex` or installs the middleware program (`:1983-1988`, `:1772-1803`) | `QueueOk.payload`: `ex` at `Γ id` (row 133) |
| `registrationDone race` | the marker's head only (`CommandAuthorityR`); replaced by the settle program, or parked (`:1912-1931`) | `RegistrationState`: the race token's result meets the saved stack |
| `afterInterrupt host kind` | no: replaced by `asVoid(awaitCode kind)` (`:1939-1944`) | `QueueOk.delivery`: `AfterInterruptReply`, `StackReply` |
| `raceCancel race host` | no: walks to `afterInterrupt host (awaitAll visited)` (`:1945-1955`) | `QueueOk.delivery`: `FiberListColumns`, `StackReply unit` |
| `closeParAwait host fibers` | no: pushes the iterator frame, installs the await-all park (`:1971-1979`) | `QueueOk.delivery`: the iterator protocol, `StackReply` |

No other command reads a running fiber's code: `evaluate` reads the flags and is a no-op on a
running fiber (`:1849-1856`); `resume` overwrites a parked fiber's code (`:1865-1878`); `launch` and
`enrollRace` spawn and observe while the host waits for its `registrationDone` (`:1879-1911`);
`interruptTarget` records an interrupt and overwrites only an idle interruptible target's code
(`interruptRecord`, `:803-824`); `trackChild`, `observe`, `exitDone`, `link`, `drainDue` and `wake`
read no code. A fiber whose current code is a race registration marker is typed by
`RegistrationState`, not by `TypedProg`: `beginRace` alone installs the marker
(`Laws/Program/InterpR.lean:320`), so both code clauses skip it.

All eighteen command-preservation declarations, `decision_preserves`, `typedState_reachable` and
`typedState_load` (M5) remain obligations. This module proves the adapters between them and the
lift, never a command case.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-- The type a position is expected at: the root's and each fiber's declared type (D7). -/
def expectOf (w : World) : Expect → Option EffTy
  | .root => w.Γ Api.root
  | .fiber id => w.Γ id
  | .hook _ => none

/-- A completion at an effect type: an exit strongly, a reference completion through the
heap table. The declared cell type is compared in the checker's order (decisions row 137:
`sub (normalize a) (normalize b)`, `Program/Checker.lean:222`; seat A's `Ty.subN` names it). -/
def CompletionStrong (w : World) (ty : EffTy) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit ex => ExitOk w ty ex
  | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.normalize.sub ty.answer.normalize = true

/-- A capture's release is admitted: its path addresses an `acquireRelease` the checker types
under an environment its values fit, extended by the acquired value, and its context's
services are typed. -/
def CaptureTyped (root : ProgramSource) (w : World) (c : Capture) : Prop :=
  ∃ (acquire release : NativeEff) (env : List Ty) (t a : EffTy),
    Node.at_ (.eff root.program) c.path = some (.eff (.acquireRelease acquire release)) ∧
    Checker.check (nativeSignature root.table) env c.path (.acquireRelease acquire release) = .ok t ∧
    Checker.check (nativeSignature root.table) env (c.path ++ [0]) acquire = .ok a ∧
    EnvTyped w (env ++ [a.answer]) c.env ∧ ServicesFit w c.ctx.services

/-- The saved stack and its provenance at a position: the stack composes from some intermediate
type to the position's declared type, and recorded causes are interrupts. Current code is not part
of it: `LiveCode` and `ReadCode` type it where it is read. -/
def SavedPosition (root : ProgramSource) (w : World) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

/-- The generated bundle, instantiated with the strong judgments once. It depends on neither the
machine nor the queue, so a step that leaves a field alone leaves its clause alone. -/
def preds (root : ProgramSource) : Preds World where
  SavedOk w e x := ∀ ty, expectOf w e = some ty → SavedPosition root w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → ExitOk w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProg root) w target token code
  ServiceOk w _ ctx := ServicesFit w ctx.services
  RaceOk w _ races := ∀ r ∈ races, ∃ resultTy, RacePayload root w r resultTy
  PromiseTable w s := ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
    CompletionStrong w ty o.code
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → Fits w v ty
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c
  CaptureOk w _ c := CaptureTyped root w c

/-- A fully typed saved frame, code included, gives its saved position. -/
theorem savedPosition_of_saved (root : ProgramSource) (w : World) (final : EffTy) (saved : RSaved)
    (typed : Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final saved) :
    SavedPosition root w final saved := by
  obtain ⟨tin, _, stack, provenance⟩ := typed
  exact ⟨tin, stack, provenance⟩

/-- The active park and saved stack agree on what the declared token delivers. -/
def ActiveDelivery (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

/-- The generated whole-state predicate and the correlations: world validity, every generated
typed position, active delivery, the settled native guard conditions, and the exact
observer/pending and registration correlations. It reads no queue and no current code (`J` adds
`LiveCode`, `I` adds `ReadCode`). Internal key bounds live here, so every command obligation's
input and output carry them. -/
def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

/-- PendingOk supplies a declaration; WorldValid bounds all declarations. -/
theorem pending_below (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (typed : TypedState root rootTy w m) (f : RFiber) (hf : f ∈ m.fibers)
    (p : Pending EffName Val Err Defect FiberId Ann) (hp : p ∈ f.pending) :
    p.token < m.nextToken := by
  obtain ⟨id, declared⟩ := (typed.2.1.c0 f hf).c1 p hp
  cases h : w.Θ id p.token with
  | none => rw [h] at declared; cases declared
  | some tokenTy => exact typed.1.tokenBound id p.token tokenTy h

/-- M6's reference runner has no host table, so its tapes contain no host answer.
Clock advances, dispatcher decisions and interrupts remain in scope (row 95). -/
def NoHostAnswer : Api.Decision → Prop
  | .answerAsync _ _ _ => False
  | _ => True

/-- A state a tape with no host answer reaches from the loaded program. -/
def RReachable (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, (∀ d ∈ tape, NoHostAnswer d) ∧ m = (replayR root.program fuel tape).machine

/-- A host answer is admitted: an answer to a fiber parked at that token fits the token's
declared type. Answers to anything else run inertly and impose nothing. -/
def AnswerOk (w : World) (m : RState) : Api.Decision → Prop
  | .answerAsync target token answer =>
    (∃ f, m.fiber? target = some f ∧ f.parked = .withGuard token) →
      ∃ ty, w.Θ target token = some ty ∧ CompletionStrong w ty answer
  | _ => True

/-- Every queued command's generated content judgment, scheduler authority and keys, plus
observer and enrollment payload correlation. The code a queued `loop` or `deliver` reads is
`ReadCode`'s, beside this structure in `ConfigTyped`. The direct forbidden afterInterrupt race
form is recorded separately and exactly. -/
structure QueueOk (root : ProgramSource) (w : World) (m : RState)
    (commands : List RCmd) : Prop where
  payload : ∀ command ∈ commands, RCmdOk (preds root) w command
  authority : ∀ command ∈ commands, CommandAuthorityR m command
  delivery : ∀ command ∈ commands, CommandDeliveryOk root w m command
  owners : (commands.filterMap (Guard.commandOwner m)).Nodup
  registration : Guard.RegistrationQueue.RegistrationQueue commands
  keys : ReservedKeysR m (commands.flatMap Guard.commandKeys)
  observer : ∀ source exit observer, .observe source exit observer ∈ commands →
    ObserverCommandOk root w m source exit observer
  enroll : ∀ race child, .enrollRace race child ∈ commands → EnrollRaceOk root w m race child
  noRaceAfterInterrupt : ∀ host yielding race,
    .afterInterrupt host yielding (.race race) ∉ commands

theorem QueueOk.fresh {root : ProgramSource} {w : World} {m : RState} {commands : List RCmd}
    (queue : QueueOk root w m commands) : QueueFresh m commands := queue.keys.below

/-! ## Row 134: the split keyed on `running` -/

/-- A queued `loop` or `deliver` will read this fiber's current code: the only two commands
that do (the table in the module header). -/
def ReadsCode (id : FiberId) (commands : List RCmd) : Prop :=
  ∃ yielding, Cmd.loop id yielding ∈ commands ∨ Cmd.deliver id yielding ∈ commands

/-- `J`'s code clause: the current code of every fiber that has not exited and is not running
is typed with its stack at the fiber's declared type. An exited fiber's code slot is never read
again (`E4-TYPED-CE-011`'s finished run); a running fiber's code is read only by the queued
command that continues it, which a budget cut may have dropped. A race registration marker is
`RegistrationState`'s. -/
def LiveCode (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → f.running = false → raceRegistrationR f.frame.current = none →
    ∀ ty, w.Γ f.id = some ty →
      Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty f.frame

/-- `I`'s code clause for running fibers: a running fiber whose current code a queued `loop` or
`deliver` reads is typed with its stack at its declared type. A running fiber continued by
`finish`, the race commands or the interrupt commands is typed by their own facts (`QueueOk`,
`RegistrationState`; the module header's table); one that no queued command continues is
inert. -/
def ReadCode (root : ProgramSource) (w : World) (m : RState) (commands : List RCmd) : Prop :=
  ∀ f ∈ m.fibers, f.running = true → ReadsCode f.id commands →
    raceRegistrationR f.frame.current = none → ∀ ty, w.Γ f.id = some ty →
      Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty f.frame

/-- Row 139's halting freedom and liveness, on the machine alone. -/
structure MachineLive (m : RState) : Prop where
  /-- The machine has not halted (`E4-TYPED-CE-014`): every halting arm of a command is an
  obligation of that command's preservation proof. -/
  running : m.stuck = none

/-- **`J`**, the machine-only typed state (decisions row 134): what every reachable machine
carries, a budget cut included. -/
structure MachineTyped (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) :
    Prop where
  typed : TypedState root rootTy w m
  code : LiveCode root w m
  live : MachineLive m

/-- **`I`**, the typed configuration (decisions row 134): the machine with the residue the
command loop runs. -/
structure ConfigTyped (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (commands : List RCmd) : Prop where
  machine : MachineTyped root rootTy w m
  code : ReadCode root w m commands
  queue : QueueOk root w m commands

/-- `J` after a step is part of `I` after it: the re-establishment the lift's `Guarded` needs is
this projection. -/
theorem machineTyped_of_configTyped {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {commands : List RCmd} (typed : ConfigTyped root rootTy w m commands) :
    MachineTyped root rootTy w m := typed.machine

/-- A halted machine is outside `J` (row 139; probe C's `typedState_halt`, read at `J`). -/
theorem machineTyped_not_halted (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (why : Stuck) : ¬ MachineTyped root rootTy w (m.halt why) := by
  intro typed
  have running : (m.halt why).stuck = none := typed.live.running
  cases running

/-- **The loop-entry premise holds for this split** (`DecisionLift.evaluate`): `J` gives `I` at
the fresh queue an evaluate or interrupt decision starts, at every machine, a budget cut
included. The proofs seat's split keyed on a queued `finish` fails exactly here
(`Test/Counterexamples/Machine/Semantics/StaleCode.lean`, `seat_split_not_decisionLift`). -/
theorem evaluate_entry (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (id : FiberId) (typed : MachineTyped root rootTy w m) :
    ConfigTyped root rootTy w m [Cmd.evaluate id, Cmd.drainDue] := by
  refine ⟨typed, ?_, ⟨?_, ?_, ?_, List.nodup_nil, ⟨trivial, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · rintro f _ _ ⟨yielding, member | member⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
  · intro command member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  · intro command member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  · intro command member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  · intro key member
    cases member
  · intro fiber token request _ member
    cases member
  · intro source exit observer member
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
  · intro race child member
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
  · intro host yielding race member
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member

/-- One dispatched command keeps the typed configuration at some later world. The dispatch
premise `m.stuck = none` is the one `Machine.Lift.StepKeeps` and `driveState` use; `I`'s own
`stuck = none` makes every halting arm of the command an obligation of its proof. -/
def StepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, m.stuck = none → ConfigTyped root rootTy w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w' r.1 r.2

/-- The eighteen command facts, once proved, are exactly the generic loop premise over `I`.
This adapter proves no individual command fact. -/
theorem stepKeeps_of_stepPreserves (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command) :
    letI := termEvaluatorFor root.program
    Machine.Lift.StepKeeps hostOrder (interpR root.program) (ConfigTyped root rootTy) := by
  letI := termEvaluatorFor root.program
  intro w m command rest running typed
  exact steps command w m rest running typed

/-- The typed configuration through the actual command loop, including its halt boundary.
All eighteen `StepPreserves` facts remain hypotheses. -/
theorem driveState_typed_of_stepPreserves (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command)
    (fuel : Nat) (w : World) (m : RState) (commands : List RCmd)
    (typed : ConfigTyped root rootTy w m commands) :
    letI := termEvaluatorFor root.program
    let result := driveState (interpR root.program) fuel m commands
    ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w' result.1 result.2 := by
  letI := termEvaluatorFor root.program
  exact Machine.Lift.driveState_lift hostOrder (interpR root.program) (ConfigTyped root rootTy)
    (stepKeeps_of_stepPreserves root rootTy steps) fuel w m commands typed

/-! ## The fire snapshot rides as a suffix of the queue

A `fire` drains a dispatcher and holds the tasks outside the machine and the queue while it runs
them (`Machine/Fibers.lean:2026-2045`); `Lift.Guarded`'s `O` types them. A task's commands are an
`evaluate`, a `resume` or a `wake`, then the due drain: none has an owner, reads code, registers a
race or names a scope. So `I` over the queue followed by the snapshot's commands is `I` over the
queue and the snapshot's queue facts, and the frame law `driveStep_append` carries the snapshot
through every command. -/

abbrev RTask := Machine.Task EffName EffThunk Val Err Defect FiberId Ann RProgram

/-- `Lift.Guarded`'s `O` for the typed state: the drained, not yet run tasks' commands are a
typed queue on the current machine. -/
def SnapshotTyped (root : ProgramSource) (w : World) (m : RState) (tasks : List RTask) : Prop :=
  QueueOk root w m (tasks.flatMap taskCmds)

/-- A task's commands: an `evaluate`, a `resume` or a `wake`, then the due drain. -/
theorem mem_taskCmds {command : RCmd} {tasks : List RTask}
    (member : command ∈ tasks.flatMap taskCmds) :
    (∃ child, command = .evaluate child) ∨ (∃ target token code, command = .resume target token code) ∨
      (∃ list phase, command = .wake list phase) ∨ command = .drainDue := by
  obtain ⟨task, _, inTask⟩ := List.mem_flatMap.mp member
  cases task with
  | start child =>
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at inTask
    rcases inTask with rfl | rfl
    · exact Or.inl ⟨child, rfl⟩
    · exact Or.inr (Or.inr (Or.inr rfl))
  | resume target token code =>
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at inTask
    rcases inTask with rfl | rfl
    · exact Or.inr (Or.inl ⟨target, token, code, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr rfl))
  | wake list phase =>
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at inTask
    rcases inTask with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨list, phase, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- A task command has no owner. -/
theorem taskCmd_owner (m : RState) {command : RCmd} {tasks : List RTask}
    (member : command ∈ tasks.flatMap taskCmds) : Guard.commandOwner m command = none := by
  rcases mem_taskCmds member with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;> rfl

/-- A task command is not a race registration's return. -/
theorem taskCmd_not_registrationDone {command : RCmd} {tasks : List RTask}
    (member : command ∈ tasks.flatMap taskCmds) (race : Nat) (yielding : Bool) :
    command ≠ .registrationDone race yielding := by
  rcases mem_taskCmds member with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;>
    exact fun h => nomatch h

/-- A task command reads no fiber's current code. -/
theorem taskCmd_not_reads {command : RCmd} {tasks : List RTask}
    (member : command ∈ tasks.flatMap taskCmds) (id : FiberId) (yielding : Bool) :
    command ≠ .loop id yielding ∧ command ≠ .deliver id yielding := by
  rcases mem_taskCmds member with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;>
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- A task command is not a registration's work (`launch`, `enrollRace`). -/
theorem taskCmd_tail {command : RCmd} {tasks : List RTask}
    (member : command ∈ tasks.flatMap taskCmds) (rest : List RCmd) :
    Guard.RegistrationQueue.RegistrationTail command rest := by
  rcases mem_taskCmds member with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;> trivial

theorem registrationTail_mono {command : RCmd} {left right : List RCmd} (subset : left ⊆ right)
    (tail : Guard.RegistrationQueue.RegistrationTail command left) :
    Guard.RegistrationQueue.RegistrationTail command right := by
  cases command with
  | launch race =>
    obtain ⟨yielding, member⟩ := tail
    exact ⟨yielding, subset member⟩
  | enrollRace race child =>
    obtain ⟨yielding, member⟩ := tail
    exact ⟨yielding, subset member⟩
  | evaluate _ => trivial
  | loop _ _ => trivial
  | deliver _ _ => trivial
  | finish _ _ => trivial
  | resume _ _ _ => trivial
  | registrationDone _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | afterInterrupt _ _ _ => trivial
  | raceCancel _ _ _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | exitDone _ => trivial
  | closeParAwait _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- Registration work keeps its return when the snapshot's commands follow the queue. -/
theorem registrationQueue_append_tasks {commands : List RCmd} {tasks : List RTask} :
    Guard.RegistrationQueue.RegistrationQueue (commands ++ tasks.flatMap taskCmds) ↔
      Guard.RegistrationQueue.RegistrationQueue commands ∧
        Guard.RegistrationQueue.RegistrationQueue (tasks.flatMap taskCmds) := by
  induction commands with
  | nil =>
    refine ⟨fun queue => ⟨trivial, queue⟩, fun queue => queue.2⟩
  | cons command rest ih =>
    constructor
    · rintro ⟨tail, queue⟩
      refine ⟨⟨?_, (ih.mp queue).1⟩, (ih.mp queue).2⟩
      cases command with
      | launch race =>
        obtain ⟨yielding, member⟩ := tail
        rcases List.mem_append.mp member with here | there
        · exact ⟨yielding, here⟩
        · exact absurd rfl (taskCmd_not_registrationDone there race yielding)
      | enrollRace race child =>
        obtain ⟨yielding, member⟩ := tail
        rcases List.mem_append.mp member with here | there
        · exact ⟨yielding, here⟩
        · exact absurd rfl (taskCmd_not_registrationDone there race yielding)
      | evaluate _ => trivial
      | loop _ _ => trivial
      | deliver _ _ => trivial
      | finish _ _ => trivial
      | resume _ _ _ => trivial
      | registrationDone _ _ => trivial
      | interruptTarget _ _ _ => trivial
      | afterInterrupt _ _ _ => trivial
      | raceCancel _ _ _ _ _ => trivial
      | trackChild _ _ => trivial
      | observe _ _ _ => trivial
      | exitDone _ => trivial
      | closeParAwait _ _ _ => trivial
      | link _ _ _ _ _ => trivial
      | drainDue => trivial
      | wake _ _ => trivial
    · rintro ⟨⟨tail, queue⟩, tasksQueue⟩
      exact ⟨registrationTail_mono (List.subset_append_left _ _) tail, ih.mpr ⟨queue, tasksQueue⟩⟩

/-- The snapshot's commands split off the queue facts. -/
theorem queueOk_append_tasks {root : ProgramSource} {w : World} {m : RState}
    {commands : List RCmd} {tasks : List RTask} :
    QueueOk root w m (commands ++ tasks.flatMap taskCmds) ↔
      QueueOk root w m commands ∧ SnapshotTyped root w m tasks := by
  have ownersNil : (tasks.flatMap taskCmds).filterMap (Guard.commandOwner m) = [] :=
    List.filterMap_eq_nil_iff.mpr fun _ member => taskCmd_owner m member
  constructor
  · intro queue
    have owners := queue.owners
    rw [List.filterMap_append, ownersNil, List.append_nil] at owners
    have regs := registrationQueue_append_tasks.mp queue.registration
    refine ⟨⟨fun c hc => queue.payload c (List.mem_append_left _ hc),
        fun c hc => queue.authority c (List.mem_append_left _ hc),
        fun c hc => queue.delivery c (List.mem_append_left _ hc), owners, regs.1,
        ⟨fun key hk => queue.keys.below key (by
            rw [List.flatMap_append]; exact List.mem_append_left _ hk),
          fun fiber token request hr hk => queue.keys.disjoint fiber token request hr (by
            rw [List.flatMap_append]; exact List.mem_append_left _ hk)⟩,
        fun s e o ho => queue.observer s e o (List.mem_append_left _ ho),
        fun r c hc => queue.enroll r c (List.mem_append_left _ hc),
        fun h y r hr => queue.noRaceAfterInterrupt h y r (List.mem_append_left _ hr)⟩,
      ⟨fun c hc => queue.payload c (List.mem_append_right _ hc),
        fun c hc => queue.authority c (List.mem_append_right _ hc),
        fun c hc => queue.delivery c (List.mem_append_right _ hc),
        by rw [ownersNil]; exact List.nodup_nil, regs.2,
        ⟨fun key hk => queue.keys.below key (by
            rw [List.flatMap_append]; exact List.mem_append_right _ hk),
          fun fiber token request hr hk => queue.keys.disjoint fiber token request hr (by
            rw [List.flatMap_append]; exact List.mem_append_right _ hk)⟩,
        fun s e o ho => queue.observer s e o (List.mem_append_right _ ho),
        fun r c hc => queue.enroll r c (List.mem_append_right _ hc),
        fun h y r hr => queue.noRaceAfterInterrupt h y r (List.mem_append_right _ hr)⟩⟩
  · rintro ⟨queue, snapshot⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, ?_,
      registrationQueue_append_tasks.mpr ⟨queue.registration, snapshot.registration⟩, ⟨?_, ?_⟩,
      fun s e o ho => ?_, fun r c hc => ?_, fun h y r hr => ?_⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact queue.payload c hc
      · exact snapshot.payload c hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact queue.authority c hc
      · exact snapshot.authority c hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact queue.delivery c hc
      · exact snapshot.delivery c hc
    · rw [List.filterMap_append, ownersNil, List.append_nil]
      exact queue.owners
    · intro key hk
      rw [List.flatMap_append] at hk
      rcases List.mem_append.mp hk with hk | hk
      · exact queue.keys.below key hk
      · exact snapshot.keys.below key hk
    · intro fiber token request hr hk
      rw [List.flatMap_append] at hk
      rcases List.mem_append.mp hk with hk | hk
      · exact queue.keys.disjoint fiber token request hr hk
      · exact snapshot.keys.disjoint fiber token request hr hk
    · rcases List.mem_append.mp ho with ho | ho
      · exact queue.observer s e o ho
      · exact snapshot.observer s e o ho
    · rcases List.mem_append.mp hc with hc | hc
      · exact queue.enroll r c hc
      · exact snapshot.enroll r c hc
    · rcases List.mem_append.mp hr with hr | hr
      · exact queue.noRaceAfterInterrupt h y r hr
      · exact snapshot.noRaceAfterInterrupt h y r hr

/-- The snapshot's commands read no code, so `ReadCode` ignores them. -/
theorem readsCode_append_tasks {id : FiberId} {commands : List RCmd} {tasks : List RTask} :
    ReadsCode id (commands ++ tasks.flatMap taskCmds) ↔ ReadsCode id commands := by
  constructor
  · rintro ⟨yielding, member | member⟩
    · rcases List.mem_append.mp member with here | there
      · exact ⟨yielding, Or.inl here⟩
      · exact absurd rfl (taskCmd_not_reads there id yielding).1
    · rcases List.mem_append.mp member with here | there
      · exact ⟨yielding, Or.inr here⟩
      · exact absurd rfl (taskCmd_not_reads there id yielding).2
  · rintro ⟨yielding, member | member⟩
    · exact ⟨yielding, Or.inl (List.mem_append_left _ member)⟩
    · exact ⟨yielding, Or.inr (List.mem_append_left _ member)⟩

/-- `I` over the queue followed by the snapshot's commands is `I` over the queue and `O`. -/
theorem configTyped_append_tasks {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {commands : List RCmd} {tasks : List RTask} :
    ConfigTyped root rootTy w m (commands ++ tasks.flatMap taskCmds) ↔
      ConfigTyped root rootTy w m commands ∧ SnapshotTyped root w m tasks := by
  constructor
  · intro typed
    obtain ⟨queue, snapshot⟩ := queueOk_append_tasks.mp typed.queue
    exact ⟨⟨typed.machine, fun f hf hr reads => typed.code f hf hr (readsCode_append_tasks.mpr reads),
      queue⟩, snapshot⟩
  · rintro ⟨typed, snapshot⟩
    exact ⟨typed.machine, fun f hf hr reads => typed.code f hf hr (readsCode_append_tasks.mp reads),
      queueOk_append_tasks.mpr ⟨typed.queue, snapshot⟩⟩

/-- **`StepPreserves` is the lift's `step` premise.** The eighteen command facts give
`StepKeeps (Guarded J I O ts)` for every snapshot `ts`: the snapshot rides as a suffix of the
queue (`configTyped_append_tasks`), the frame law moves it through the command
(`Machine.Lift.driveStep_append`), and `I`'s `stuck = none` rules out the frame law's halting
alternative. `J` after the step is `I`'s projection. -/
theorem guarded_stepKeeps_of_stepPreserves (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command) (tasks : List RTask) :
    letI := termEvaluatorFor root.program
    Machine.Lift.StepKeeps hostOrder (interpR root.program)
      (Machine.Lift.Guarded (MachineTyped root rootTy) (ConfigTyped root rootTy)
        (SnapshotTyped root) tasks) := by
  letI := termEvaluatorFor root.program
  intro w m command rest running guarded
  obtain ⟨typed, snapshot⟩ := guarded.2 running
  have joined : ConfigTyped root rootTy w m (command :: (rest ++ tasks.flatMap taskCmds)) := by
    rw [← List.cons_append]
    exact configTyped_append_tasks.mpr ⟨typed, snapshot⟩
  obtain ⟨w', ordered, after⟩ := steps command w m (rest ++ tasks.flatMap taskCmds) running joined
  obtain ⟨sameMachine, residue⟩ :=
    Machine.Lift.driveStep_append (interpR root.program) m command rest (tasks.flatMap taskCmds)
  rw [sameMachine] at after
  rcases residue with residue | ⟨_, _, halted⟩
  · rw [residue] at after
    obtain ⟨typed', snapshot'⟩ := configTyped_append_tasks.mp after
    exact ⟨w', ordered, typed'.machine, fun _ => ⟨typed', snapshot'⟩⟩
  · rw [after.machine.live.running] at halted
    cases halted

/-! ## The capture lookup -/

theorem envTyped_append {w : World} {env : List Ty} {vals : List Val} {ty : Ty} {v : Val}
    (h : EnvTyped w env vals) (hv : Fits w v ty) : EnvTyped w (env ++ [ty]) (vals ++ [v]) := by
  refine ⟨by simp only [List.length_append, h.1, List.length_singleton], fun i t x ht hx => ?_⟩
  by_cases hi : i < env.length
  · rw [List.getElem?_append_left hi] at ht
    rw [List.getElem?_append_left (h.1 ▸ hi)] at hx
    exact h.2 i t x ht hx
  · have hge : env.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hge] at ht
    rw [List.getElem?_append_right (h.1 ▸ hge)] at hx
    rw [← h.1] at hx
    cases hk : i - env.length with
    | zero =>
      rw [hk] at ht hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hx
      subst ht hx
      exact hv
    | succ k =>
      rw [hk] at ht
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at ht
      cases ht

/-- A capture's release runs at the point its path's `acquireRelease` checks it at: the
release child, over the checker's environment extended by the acquired value and the exit. -/
theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (h : CaptureTyped root w c)
    (hex : Fits w exVal (.exitOf .unknown .unknown)) :
    ∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty := by
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, _⟩ := h
  obtain ⟨a', r, hacq', hrel, _, _⟩ := Checker.inv_acquireRelease _ _ _ _ _ t hcheck
  rw [hacq] at hacq'
  cases hacq'
  refine ⟨r, release, env ++ [a.answer, .exitOf .unknown .unknown], ?_, hrel, ?_⟩
  · show Node.at_ (.eff root.program) (c.path ++ [1]) = some (.eff release)
    rw [Agreement.Node.at_append, hnode]
    rfl
  · show EnvTyped w (env ++ [a.answer, .exitOf .unknown .unknown]) (c.env ++ [exVal])
    have := envTyped_append henv hex
    simpa only [List.append_assoc, List.singleton_append] using this

/-! ## The milestone propositions

Named once, so the ledger's declarations and the connectors below read the same statement. -/

/-- Rows 111–116: the source's Σ_app is lawful. Today this is the program-plane row-table check
`Table.lawful` (unique keys, no built-in collision, no dropped trailing names). Seat A's evidence
field on `ProgramSource` (row 114) supplies the service-table clauses (rows 112–114) and replaces
this body; the statements keep this premise's name, and `w.serviceTy` (row 112, shape A) joins
`MachineTyped` as the static world component tied to the source when seat A's field lands. -/
def LawfulSource (root : ProgramSource) : Prop := Table.lawful root.table = true

/-- M5's proposition: a lawful, checked, closed source loads into `J`. -/
def LoadsTyped (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) : Prop :=
  LawfulSource root → Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
    ∃ w, MachineTyped root rootTy w (loadR root.program fuel compileFuel)

/-- M6b's proposition: one tape decision keeps `J` when its host answer, if any, is admitted. -/
def DecisionKeeps (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    Prop :=
  ∀ w m, MachineTyped root rootTy w m → AnswerOk w m d →
    ∃ w', w.leHost w' ∧ MachineTyped root rootTy w'
      (letI := termEvaluatorFor root.program
       stepDecisionState (interpR root.program) fuel m d).1

/-- M6c's proposition: every machine an answer-free tape reaches from a lawful, checked, closed
source is in `J`. -/
def ReachableTyped (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) : Prop :=
  LawfulSource root → Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
    RReachable root fuel m → ∃ w, MachineTyped root rootTy w m

/-- A tape with no host answer is admitted at every machine it meets. -/
theorem admittedReplay_noHostAnswer (root : ProgramSource) (J : World → RState → Prop)
    (fuel : Nat) :
    ∀ (tape : List Api.Decision), (∀ d ∈ tape, NoHostAnswer d) → ∀ m : RState,
      letI := termEvaluatorFor root.program
      Machine.Lift.AdmittedReplay J (fun w m d => AnswerOk w m d) (interpR root.program) fuel m tape
  | [], _, _ => trivial
  | d :: tape, free, m => by
    intro _
    refine ⟨fun w _ => ?_, fun _ => admittedReplay_noHostAnswer root J fuel tape
      (fun d' hd' => free d' (List.mem_cons_of_mem _ hd')) _⟩
    have hd := free d List.mem_cons_self
    cases d with
    | answerAsync id token answer => exact hd.elim
    | fire owner => trivial
    | flush => trivial
    | evaluate id => trivial
    | yieldVerdict id verdict => trivial
    | interruptFrom who extra target => trivial
    | installMiddleware => trivial
    | advance millis => trivial

/-- **M6c from M5 and M6b**, through the replay lift (`Machine.Lift.replayEval_lift`). -/
theorem reachable_of_ledger (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (load : LoadsTyped root rootTy fuel fuel) (decisions : ∀ d, DecisionKeeps root rootTy fuel d)
    (m : RState) : ReachableTyped root rootTy fuel m := by
  rintro lawful checked closed ⟨tape, free, rfl⟩
  obtain ⟨w₀, loaded⟩ := load lawful checked closed
  letI := termEvaluatorFor root.program
  obtain ⟨w, _, typed⟩ := Machine.Lift.replayEval_lift hostOrder (MachineTyped root rootTy)
    (fun w m d => AnswerOk w m d) (interpR root.program) fuel
    (fun w m d _ held admitted => decisions d w m held admitted) tape w₀
    (loadR root.program fuel fuel) loaded
    (admittedReplay_noHostAnswer root (MachineTyped root rootTy) fuel tape free _)
  exact ⟨w, typed⟩

/-! ## M7: the frame machine's observation is typed (decisions row 138)

M7 transfers `J` from the term reference to the frame machine that runs `compileEff`'s first-order
code (`Api.replay`) along `run_eq_ref`'s relation (`replay_rel`, `BMeans`): every exit the
observation `obs` records fits its fiber's declared type (M7a), the stores fit (M7b), and the run
never halts (M7c). The fragment is `run_eq_ref`'s: the empty host table, the empty oracle,
answer-free tapes, every command budget, the compile budget equal to it. M7 is about the frame
machine, not "the compiled machine": the OCaml engine (the LCNF route) is outside it until
decisions row 28 is ruled, and nothing here is verified lowering or host safety.

**R1's exception** (decisions row 138, ruled 2026-10-01; system map §8): M7 holds over the service
half of Σ_app with the row table fixed empty. The table-aware agreement (DI-57's host-free part:
external registration, evaluator selection) belongs to R6, after M7
(`Test/contracts/machine-scheduler-core.contract.md`, "Table-aware agreement (DI-57)").

The route is proved here (`m7_of_ledger`): from `typedState_load` and `decision_preserves`,
through `replayEval_lift`, to `J` on the reference replay, then across `BMeans`
(`bookMeans_obs`, `BookMeans.stuck`). M7a–c stay open while M5 and M6 are. -/

/-- The M7 fragment: a lawful source at the empty host table, checked and closed, and a tape with
no host answer. -/
structure M7Fragment (root : ProgramSource) (rootTy : EffTy) (tape : List Api.Decision) :
    Prop where
  lawful : LawfulSource root
  emptyTable : root.table = []
  checked : Api.typeOf root.program root.table = some rootTy
  closed : ClosedEff rootTy
  answerFree : ∀ d ∈ tape, NoHostAnswer d

/-- M7a's conclusion on an observation: the root is declared at the program's type, the world's
store is the observed one, and every recorded exit fits its fiber's declared type. -/
def ExitsFit (rootTy : EffTy) (w : World) (o : Obs) : Prop :=
  w.Γ Api.root = some rootTy ∧ w.state = o.stores ∧
    ∀ id ex, (id, some ex) ∈ o.exits → ∃ ty, w.Γ id = some ty ∧ ExitOk w ty ex

/-- M7b's conclusion: the observed stores fit at a world that describes them exactly. -/
def StoresFit (root : ProgramSource) (w : World) (s : Stores) : Prop :=
  w.state = s ∧ s.WF ∧ (∀ key, (w.Ρ key).isSome = true ↔ key.index < s.refs.length) ∧
    (∀ key, (w.«Π» key).isSome = true ↔ key.index < s.deferreds.cells.length) ∧
    StoresOk (preds root) w Expect.root s

/-- M7a's proposition. -/
def M7Exits (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision) :
    Prop :=
  M7Fragment root rootTy tape →
    ∃ w, ExitsFit rootTy w (obs (Api.replay root.program fuel tape).machine)

/-- M7b's proposition. -/
def M7Stores (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision) :
    Prop :=
  M7Fragment root rootTy tape →
    ∃ w, StoresFit root w (obs (Api.replay root.program fuel tape).machine).stores

/-- M7c's proposition: the frame machine never halts on the fragment. -/
def M7NoHalt (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision) :
    Prop :=
  M7Fragment root rootTy tape → (Api.replay root.program fuel tape).machine.stuck = none

/-- `J` on a reference machine types its observation: the exits and the stores. -/
theorem obsTyped_of_machineTyped {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) :
    ExitsFit rootTy w (obs m) ∧ StoresFit root w (obs m).stores := by
  obtain ⟨⟨valid, ok, _, _, _, _⟩, _, _⟩ := typed
  refine ⟨⟨valid.root, valid.state, fun id ex member => ?_⟩,
    valid.state, valid.wf, valid.heap, valid.promises, ok.c2⟩
  obtain ⟨f, hf, same⟩ := List.mem_map.mp member
  obtain ⟨hid, hex⟩ := Prod.mk.inj same
  obtain ⟨ty, declared⟩ := Option.isSome_iff_exists.mp
    ((valid.fibers f.id).mpr (List.mem_map_of_mem hf))
  refine ⟨ty, hid ▸ declared, (ok.c0 f hf).c3 ex hex ty declared⟩

/-- The frame machine's replay halts exactly when the term reference's replay of the same tape
does: `run_eq_ref`'s relation equates `stuck` (`BookMeans.stuck`). -/
theorem replay_stuck_eq (e : NativeEff) (fuel : Nat) (tape : List Api.Decision) :
    (Api.replay e fuel tape).machine.stuck = (replayR e fuel tape).machine.stuck := by
  rw [replay_machine]
  exact (ReplayRel.machine (replay_rel e fuel fuel tape)).stuck

/-- **M7's route from the capstone.** `J` on the reference replay of every answer-free tape gives
M7a–c on the frame machine's replay of the same tape. -/
theorem m7_of_capstone (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (tape : List Api.Decision) (capstone : ∀ m, ReachableTyped root rootTy fuel m) :
    M7Exits root rootTy fuel tape ∧ M7Stores root rootTy fuel tape ∧
      M7NoHalt root rootTy fuel tape := by
  have transfer : M7Fragment root rootTy tape → ∃ w,
      MachineTyped root rootTy w (replayR root.program fuel tape).machine ∧
      obs (Api.replay root.program fuel tape).machine = obs (replayR root.program fuel tape).machine ∧
      (Api.replay root.program fuel tape).machine.stuck =
        (replayR root.program fuel tape).machine.stuck := by
    intro fragment
    obtain ⟨w, typed⟩ := capstone _ fragment.lawful fragment.checked fragment.closed
      ⟨tape, fragment.answerFree, rfl⟩
    have related := ReplayRel.machine (replay_rel root.program fuel fuel tape)
    refine ⟨w, typed, ?_, replay_stuck_eq root.program fuel tape⟩
    rw [replay_machine]
    exact bookMeans_obs related
  refine ⟨fun fragment => ?_, fun fragment => ?_, fun fragment => ?_⟩
  · obtain ⟨w, typed, sameObs, _⟩ := transfer fragment
    rw [sameObs]
    exact ⟨w, (obsTyped_of_machineTyped typed).1⟩
  · obtain ⟨w, typed, sameObs, _⟩ := transfer fragment
    rw [sameObs]
    exact ⟨w, (obsTyped_of_machineTyped typed).2⟩
  · obtain ⟨_, typed, _, sameStuck⟩ := transfer fragment
    rw [sameStuck]
    exact typed.live.running

/-- **M7 from the ledger** (decisions row 138's route): `typedState_load` and
`decision_preserves` at one source and budget give M7a–c at every answer-free tape. -/
theorem m7_of_ledger (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (tape : List Api.Decision) (load : LoadsTyped root rootTy fuel fuel)
    (decisions : ∀ d, DecisionKeeps root rootTy fuel d) :
    M7Exits root rootTy fuel tape ∧ M7Stores root rootTy fuel tape ∧
      M7NoHalt root rootTy fuel tape :=
  m7_of_capstone root rootTy fuel tape (reachable_of_ledger root rootTy fuel load decisions)

/-! ## R4: the reference replay is in the book with a native reachable machine

`Guard.Reachable` (`Laws/Program/Guard/Core.lean:41-44`) is the native machine's reachability:
per-decision budgets, continuing past frontiers. `RReachable` is the reference's: one budget,
stopping at the first frontier. The replay stops at a prefix of its tape, so its native machine
is a `Guard.Reachable` fold at constant budget, and `replay_rel` relates it to the reference
machine by `BMeans`, which equates every code-free field (`Laws/Machine/Book.lean:193-203`):
code-free guard facts transport to the reference for free (decisions row 140). -/

/-- `replayEval` stops at a prefix of its tape: its machine is the fold of the decisions it
applied, every one at the replay's command budget. -/
theorem replayEval_machine_prefix (e : NativeEff) (fuel : Nat) :
    ∀ (tape : List Api.Decision) (m : NativeMachine), ∃ k,
      (letI := evaluatorFor e
       (replayEval (interpOf e) fuel tape m).machine) =
        (tape.take k).foldl (fun m d => steppedBy e fuel [] m d) m
  | [], m => ⟨0, by
      letI := evaluatorFor e
      exact Machine.Lift.replayEval_nil_machine (interpOf e) fuel m⟩
  | d :: tape, m => by
    letI := evaluatorFor e
    simp only [replayEval]
    split
    · exact ⟨0, rfl⟩
    · split
      · obtain ⟨k, prefixFold⟩ :=
          replayEval_machine_prefix e fuel tape (stepDecisionState (interpOf e) fuel m d).1
        exact ⟨k + 1, prefixFold⟩
      · exact ⟨1, rfl⟩

/-- **R4's bridge.** Every machine the reference replay reaches at the empty table is related by
`BMeans` to a `Guard.Reachable` native machine: the frame machine's replay of the same tape. -/
theorem replayR_bmeans_reachable (e : NativeEff) (fuel : Nat) (tape : List Api.Decision) :
    ∃ m₁, Guard.Reachable e [] fuel [] m₁ ∧ BMeans e m₁ (replayR e fuel tape).machine := by
  letI := evaluatorFor e
  obtain ⟨k, prefixFold⟩ := replayEval_machine_prefix e fuel tape (Api.load e fuel)
  refine ⟨(Api.replay e fuel tape).machine, ⟨(tape.take k).map fun d => (fuel, d), ?_⟩, ?_⟩
  · rw [replay_machine, prefixFold]
    simp only [Guard.executePrefix, List.foldl_map]
  · rw [replay_machine]
    exact ReplayRel.machine (replay_rel e fuel fuel tape)

/-! ## Declared obligations

`typedState_load` (M5: initialization from an admitted source). The transition ledger (M6): one
preservation obligation per command constructor, one for a tape decision under admitted host
answers, and the capstone that every reachable state is typed. Declared, not proved. -/
namespace M3bAssembly

theorem typedState_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (LoadsTyped root rootTy fuel compileFuel) := ⟨⟩

theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (_h : CaptureTyped root w c)
    (_hex : Fits w exVal (.exitOf .unknown .unknown)) : ProofGraph.Obligation
    (∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty) := ⟨⟩

end M3bAssembly

namespace M6Ledger

theorem step_evaluate (root : ProgramSource) (rootTy : EffTy) (id : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.evaluate id)) := ⟨⟩

theorem step_loop (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.loop id yielding)) := ⟨⟩

theorem step_deliver (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.deliver id yielding)) := ⟨⟩

theorem step_finish (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (exit : ExitV) :
    ProofGraph.Obligation (StepPreserves root rootTy (.finish id exit)) := ⟨⟩

theorem step_resume (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (token : Nat) (code : RProgram) :
    ProofGraph.Obligation (StepPreserves root rootTy (.resume id token code)) := ⟨⟩

theorem step_launch (root : ProgramSource) (rootTy : EffTy) (race : Nat) :
    ProofGraph.Obligation (StepPreserves root rootTy (.launch race)) := ⟨⟩

theorem step_enrollRace (root : ProgramSource) (rootTy : EffTy) (race : Nat) (child : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.enrollRace race child)) := ⟨⟩

theorem step_registrationDone (root : ProgramSource) (rootTy : EffTy) (race : Nat) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.registrationDone race yielding)) := ⟨⟩

theorem step_interruptTarget (root : ProgramSource) (rootTy : EffTy) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreserves root rootTy (.interruptTarget target who extra)) := ⟨⟩

theorem step_afterInterrupt (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (kind : ParkKind) :
    ProofGraph.Obligation (StepPreserves root rootTy (.afterInterrupt host yielding kind)) := ⟨⟩

theorem step_raceCancel (root : ProgramSource) (rootTy : EffTy) (race : Nat) (host : FiberId)
    (yielding : Bool) (remaining visited : List FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.raceCancel race host yielding remaining visited)) := ⟨⟩

theorem step_trackChild (root : ProgramSource) (rootTy : EffTy) (parent child : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.trackChild parent child)) := ⟨⟩

theorem step_observe (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) (exit : ExitV) (observer : Observer) :
    ProofGraph.Obligation (StepPreserves root rootTy (.observe fiber exit observer)) := ⟨⟩

theorem step_exitDone (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.exitDone fiber)) := ⟨⟩

theorem step_closeParAwait (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (fibers : List FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.closeParAwait host yielding fibers)) := ⟨⟩

theorem step_link (root : ProgramSource) (rootTy : EffTy) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreserves root rootTy (.link mode scope target interruptor extra)) := ⟨⟩

theorem step_drainDue (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (StepPreserves root rootTy .drainDue) := ⟨⟩

theorem step_wake (root : ProgramSource) (rootTy : EffTy) (list : WakeKey) (phase : WakePhase) :
    ProofGraph.Obligation (StepPreserves root rootTy (.wake list phase)) := ⟨⟩

/-- A tape decision keeps `J` when its host answer, if any, is admitted. -/
theorem decision_preserves (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    ProofGraph.Obligation (DecisionKeeps root rootTy fuel d) := ⟨⟩

/-- The capstone obligation: every machine a tape with no host answer reaches from a lawful,
checked, closed source is in `J` (`reachable_of_ledger` derives it from `typedState_load` and
`decision_preserves`). The host-answer restriction repairs `E4-SCHED-CE-015`.

Live refutations at this commit: `E4-TYPED-CE-009` (`Fits` compares declared types in the raw
order while the checker normalizes, so M5 is false for a checked program; seat A, row 137) and
`E4-TYPED-CE-010` (the await-by-value post reads the target's answer column, so M5 is false for
the typed corpus's `awaitFiber.value`; seat B, row 136); either falsifies the capstone at the
loaded machine. `E4-TYPED-CE-011` (the saved-code clause read at a budget cut) refuted the
statement over the typed state before row 134 and is repaired by the split
(`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), as is `E4-TYPED-CE-014` (a halted
machine typed) by `J`'s `stuck = none`.

`ExitOk` excludes `badName` and `notImplemented` at typed code, saved-stack, queued-result and
stored-completion exit positions (`E4-TYPED-CE-007`); the obligations above remain open, so this
judgment alone does not establish their absence from every run. `missingService` remains
admitted at every requirement row in H2 part one; its exclusion requires row 117's
frame-and-operation contract. -/
theorem typedState_reachable (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ProofGraph.Obligation (ReachableTyped root rootTy fuel m) := ⟨⟩

end M6Ledger

/-! M7 (decisions row 138, ruled 2026-10-01): at the empty host table, on answer-free tapes, with
observation `obs`, the frame machine's run is typed. `m7_of_ledger` derives all three from
`typedState_load` and `decision_preserves`. -/
namespace M7

/-- M7a: every exit the observation records fits its fiber's declared type. -/
theorem exits_typed (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision) :
    ProofGraph.Obligation (M7Exits root rootTy fuel tape) := ⟨⟩

/-- M7b: the observed stores fit at a world that describes them. -/
theorem stores_typed (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision) :
    ProofGraph.Obligation (M7Stores root rootTy fuel tape) := ⟨⟩

/-- M7c: the frame machine never halts on the fragment (row 139's `stuck = none` in `J`). -/
theorem never_halts (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision) :
    ProofGraph.Obligation (M7NoHalt root rootTy fuel tape) := ⟨⟩

end M7

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M3bAssembly.capture_lookup :=
  @Effect4.Program.Typed.capture_lookup
#proof_wanted Effect4.Program.Typed.M3bAssembly.typedState_load
#typed_state_obligations Effect4.Program.Typed.M3bAssembly ceiling 1
  using aesop (rule_sets := [Effect4.TypedState])
#proof_wanted Effect4.Program.Typed.M6Ledger.step_evaluate
#proof_wanted Effect4.Program.Typed.M6Ledger.step_loop
#proof_wanted Effect4.Program.Typed.M6Ledger.step_deliver
#proof_wanted Effect4.Program.Typed.M6Ledger.step_finish
#proof_wanted Effect4.Program.Typed.M6Ledger.step_resume
#proof_wanted Effect4.Program.Typed.M6Ledger.step_launch
#proof_wanted Effect4.Program.Typed.M6Ledger.step_enrollRace
#proof_wanted Effect4.Program.Typed.M6Ledger.step_registrationDone
#proof_wanted Effect4.Program.Typed.M6Ledger.step_interruptTarget
#proof_wanted Effect4.Program.Typed.M6Ledger.step_afterInterrupt
#proof_wanted Effect4.Program.Typed.M6Ledger.step_raceCancel
#proof_wanted Effect4.Program.Typed.M6Ledger.step_trackChild
#proof_wanted Effect4.Program.Typed.M6Ledger.step_observe
#proof_wanted Effect4.Program.Typed.M6Ledger.step_exitDone
#proof_wanted Effect4.Program.Typed.M6Ledger.step_closeParAwait
#proof_wanted Effect4.Program.Typed.M6Ledger.step_link
#proof_wanted Effect4.Program.Typed.M6Ledger.step_drainDue
#proof_wanted Effect4.Program.Typed.M6Ledger.step_wake
#proof_wanted Effect4.Program.Typed.M6Ledger.decision_preserves
#proof_wanted Effect4.Program.Typed.M6Ledger.typedState_reachable
#typed_state_obligations Effect4.Program.Typed.M6Ledger ceiling 20
  using aesop (rule_sets := [Effect4.TypedState])
#proof_wanted Effect4.Program.Typed.M7.exits_typed
#proof_wanted Effect4.Program.Typed.M7.stores_typed
#proof_wanted Effect4.Program.Typed.M7.never_halts
#typed_state_obligations Effect4.Program.Typed.M7 ceiling 3
  using aesop (rule_sets := [Effect4.TypedState])
