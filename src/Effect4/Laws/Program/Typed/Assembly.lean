import Effect4.Laws.Program.Typed.Stack
import Effect4.Laws.Machine.Lift
import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Program.Typed.Scheduler
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.ReferenceTyping

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

The ledger is the one list (decisions row 140): M5 (`M3bAssembly`: `typedState_load`,
`denoteR_typed`, `evalTerm_fits`), M6 (`M6Ledger`: the eighteen command obligations,
`decision_preserves`, `typedState_reachable`), the decision edits and the fire snapshot
(`M6Edits`: `DecisionLift`'s fields other than `step`, and the split's re-establishment), stack
monotonicity (`M6Stack`, until seat B's `M3bWorld` states it) and M7 (`M7`: a–c and scope-handle
validity). The eighteen, `decision_preserves`, `typedState_reachable` and `typedState_load` remain
obligations. This module proves the adapters between them and the lift, the six bookkeeping
edits, M5's builder (`machineTyped_load`) and its reduction to `denoteR_typed`
(`loadsTyped_of_denotesTyped`), never a command case.
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
machine nor the queue, so a step that leaves a field alone leaves its clause alone. A closed
scope's exit fits DI-94's release type `Exit<unknown, unknown>` (decisions row 140): its values
are live, `Fits`' `unknown` arm. -/
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
  ScopeExitOk w _ ex := Fits w (reifyExitVal ex) (.exitOf .unknown .unknown)

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
observer and enrollment payload correlation and the liveness of a queued link. The code a queued
`loop` or `deliver` reads is `ReadCode`'s, beside this structure in `ConfigTyped`. The direct
forbidden afterInterrupt race form is recorded separately and exactly. -/
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
  /-- A queued `link` names a scope the store holds and an existing target: `linkScope` halts
  otherwise (`Machine/Fibers.lean:1005-1036`). Row 139's typed scope on a queued link. -/
  links : ∀ mode scope target interruptor extra,
    .link mode scope target interruptor extra ∈ commands →
      (m.state.scopes.entryAt scope).isSome = true ∧ (m.fiber? target).isSome = true

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

/-- Row 139's halting freedom and liveness, on the machine alone. Each clause names the halting
arm it rules out; with the scope-finalizer drops of `ObserverState` and `QueueOk.observer`, with
`QueueOk.links` (in `I`) and a scope-liveness premise on the scope-reading fiber rows (seat B's
`fiberPre`, pending: `M6Capstone.step_deliver_refuted_by_absent_scope`) they are what each command
proof needs to show its halting arms unreachable. Race-id liveness for the
codes that name a race is `RegistrationState` (in `TypedState`): the only race halt is
`registerRace` on a registration marker (`Machine/Fibers.lean:937-944`), and both code clauses
leave the marker to it. A fiber handle's liveness is `Fits`'s fiber arm with
`WorldValid.fibers`. -/
structure MachineLive (m : RState) : Prop where
  /-- The machine has not halted (`E4-TYPED-CE-014`): every halting arm of a command is an
  obligation of that command's preservation proof. -/
  running : m.stuck = none
  /-- `forkScoped` links the child into the context's ambient scope (`:1474-1489`; `linkScope`,
  `:1005-1036`). The scope arm of `HandleFits` reading the scope store (seat A) makes
  `ServiceOk` carry this for every typed context; until it lands the clause is stated here. -/
  ambientScopes : ∀ f ∈ m.fibers, ∀ scope, Ctx.ambientScope f.context = some scope →
    (m.state.scopes.entryAt scope).isSome = true
  /-- `drainOwed` posts a scheduled resume on its owner's dispatcher and halts on an absent owner
  (`postTask`, `:709-716`). Today's stores owe only `now` resumes (`DeferredStore.due`,
  `Machine/Stores.lean:1090`), so this holds vacuously on reachable machines. -/
  dueOwners : ∀ o ∈ m.state.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
    (m.fiber? owner).isSome = true

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
  refine ⟨typed, ?_, ⟨?_, ?_, ?_, List.nodup_nil, ⟨trivial, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
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
  · intro mode scope target interruptor extra member
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

/-- A task command is not a scope link. -/
theorem taskCmd_not_link {command : RCmd} {tasks : List RTask}
    (member : command ∈ tasks.flatMap taskCmds) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    command ≠ .link mode scope target interruptor extra := by
  rcases mem_taskCmds member with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;>
    exact fun h => nomatch h

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
        fun h y r hr => queue.noRaceAfterInterrupt h y r (List.mem_append_left _ hr),
        fun md sc tg ir ex hl => queue.links md sc tg ir ex (List.mem_append_left _ hl)⟩,
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
        fun h y r hr => queue.noRaceAfterInterrupt h y r (List.mem_append_right _ hr),
        fun md sc tg ir ex hl => queue.links md sc tg ir ex (List.mem_append_right _ hl)⟩⟩
  · rintro ⟨queue, snapshot⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, ?_,
      registrationQueue_append_tasks.mpr ⟨queue.registration, snapshot.registration⟩, ⟨?_, ?_⟩,
      fun s e o ho => ?_, fun r c hc => ?_, fun h y r hr => ?_, fun md sc tg ir ex hl => ?_⟩
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
    · rcases List.mem_append.mp hl with hl | hl
      · exact queue.links md sc tg ir ex hl
      · exact absurd rfl (taskCmd_not_link hl md sc tg ir ex)

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

/-! ## `J` and the queue facts move between machines with the same view

`J` reads a machine only through its fibers, races, store, the three counters and `stuck`; a
decision's trace, latch and arming edits change none of them. One congruence lemma carries `J`
across every such edit, instead of a rebuild per edit. -/

theorem machineTyped_congr {root : ProgramSource} {rootTy : EffTy} {w : World} {m m' : RState}
    (fibers : m'.fibers = m.fibers) (races : m'.races = m.races) (state : m'.state = m.state)
    (nextId : m'.nextId = m.nextId) (nextToken : m'.nextToken = m.nextToken)
    (nextRace : m'.nextRace = m.nextRace) (stuck : m'.stuck = m.stuck)
    (typed : MachineTyped root rootTy w m) : MachineTyped root rootTy w m' := by
  obtain ⟨⟨valid, ok, deliv, sched, obsv, reg⟩, code, live⟩ := typed
  have member : ∀ f, f ∈ m'.fibers → f ∈ m.fibers := fun f hf => by rw [← fibers]; exact hf
  have raceMember : ∀ r, r ∈ m'.races → r ∈ m.races := fun r hr => by rw [← races]; exact hr
  have lookup : ∀ id, m'.fiber? id = m.fiber? id := fun id => by
    unfold RunMachine.fiber?
    rw [fibers]
  have raceLookup : ∀ r, m'.race? r = m.race? r := fun r => by
    unfold RunMachine.race?
    rw [races]
  have requests : ∀ fiber token, requestOfR m' fiber token = requestOfR m fiber token :=
    fun fiber token => by
      unfold requestOfR
      rw [lookup]
  have keys : Guard.internalKeys m' = Guard.internalKeys m := by
    unfold Guard.internalKeys
    rw [state, races, fibers]
  refine ⟨⟨?_, ⟨fun f hf => ok.c0 f (member f hf), ?_, ?_⟩,
    fun f hf token parked => deliv f (member f hf) token parked, ?_,
    ⟨fun f hf => obsv.pendingOwner f (member f hf), fun f hf o ho =>
      storedObserverOk_congr lookup raceLookup state o (obsv.observers f (member f hf) o ho)⟩,
    fun f hf raceId marker => ?_⟩, fun f hf => code f (member f hf), ?_⟩
  · exact
      { ids := by rw [fibers]; exact valid.ids
        fibers := fun id => by rw [fibers]; exact valid.fibers id
        heap := fun key => by rw [state]; exact valid.heap key
        promises := fun key => by rw [state]; exact valid.promises key
        tokens := fun f hf token parked => valid.tokens f (member f hf) token parked
        tokenBound := fun id token ty h => by rw [nextToken]; exact valid.tokenBound id token ty h
        tokenTargets := valid.tokenTargets
        state := by rw [state]; exact valid.state
        wf := by rw [state]; exact valid.wf
        cells := valid.cells
        fiberClosed := valid.fiberClosed
        heapClosed := valid.heapClosed
        promiseClosed := valid.promiseClosed
        tokenClosed := valid.tokenClosed
        root := valid.root }
  · rw [races]
    exact ok.c1
  · rw [state]
    exact ok.c2
  · exact
      { fiberIds := by rw [fibers]; exact sched.fiberIds
        fibersBelow := fun f hf => by rw [nextId]; exact sched.fibersBelow f (member f hf)
        raceIds := by rw [races]; exact sched.raceIds
        racesBelow := fun r hr => by rw [nextRace]; exact sched.racesBelow r (raceMember r hr)
        raceHosts := fun r hr => by
          obtain ⟨f, found⟩ := sched.raceHosts r (raceMember r hr)
          exact ⟨f, (lookup r.host).trans found⟩
        keysBelow := fun key hk => by
          rw [keys] at hk
          rw [nextToken]
          exact sched.keysBelow key hk
        requestsBelow := fun fiber token request hr => by
          rw [requests] at hr
          rw [nextToken]
          exact sched.requestsBelow fiber token request hr
        requestsOwned := fun fiber token request hr => by
          rw [requests] at hr
          rw [keys]
          exact sched.requestsOwned fiber token request hr
        pendingShape := fun f hf => sched.pendingShape f (member f hf)
        parkedIdle := fun f hf => sched.parkedIdle f (member f hf)
        parkedBelow := fun f hf token parked => by
          rw [nextToken]
          exact sched.parkedBelow f (member f hf) token parked
        exited := fun f hf => sched.exited f (member f hf)
        deferredCause := fun f hf => sched.deferredCause f (member f hf) }
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := reg f (member f hf) raceId marker
    exact ⟨race, resultTy, (raceLookup raceId).trans found, host, token, reply⟩
  · refine ⟨stuck.trans live.running, fun f hf scope ambient => ?_, fun o ho owner priority mode => ?_⟩
    · rw [state]
      exact live.ambientScopes f (member f hf) scope ambient
    · rw [state] at ho
      rw [lookup]
      exact live.dueOwners o ho owner priority mode

/-- The queue facts survive a trace edit: an `emit` changes no lookup, counter or store. -/
theorem queueOk_emit {root : ProgramSource} {w : World} {m : RState} {commands : List RCmd}
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit))
    (queue : QueueOk root w m commands) : QueueOk root w (m.emit events) commands :=
  { payload := queue.payload, authority := queue.authority, delivery := queue.delivery,
    owners := queue.owners, registration := queue.registration,
    keys := ⟨queue.keys.below, queue.keys.disjoint⟩,
    observer := fun source exit o ho => observerCommandOk_congr (m := m) (m' := m.emit events)
      (fun _ => rfl) (fun _ => rfl) rfl o (queue.observer source exit o ho),
    enroll := queue.enroll, noRaceAfterInterrupt := queue.noRaceAfterInterrupt,
    links := queue.links }

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

/-- Row 148 (algebra A3): M5's fundamental property. A checked point denotes, at the node its
path names, a program typed at the point's certificate, at every world. -/
def DenotesTyped (root : ProgramSource) : Prop :=
  ∀ (w : World) (p : Point) (e : NativeEff) (ty : EffTy),
    Node.at_ (.eff root.program) p.path = some (.eff e) → PointTyped root w p ty →
      TypedProg root w ty (denoteR root.program e p)

/-- Row 148 (types TY-07): term soundness at `Fits`. A term the checker types evaluates, in an
environment typed at the same world, to a value that fits its type. Term typing reads only the
signature's atoms, so the statement is at any row table; seat A proves it beside
`evalTerm_hasTy` (`Laws/Program/Typed.lean`). -/
def TermFits (table : RowTable) : Prop :=
  ∀ (w : World) (env : List Ty) (vals : List Val) (t : Term) (ty : Ty) (v : Val),
    termTy (nativeSignature table) env t = some ty → EnvTyped w env vals →
      evalTerm vals t = some v → Fits w v ty

/-! ## M5 from the fundamental property

The loaded machine has one fiber, not running, whose code is the root's denotation; every other
clause of `J` is over an empty list or the empty context. So M5 is the root code's typing at
every world (`machineTyped_load`), and that is `DenotesTyped` at the root point when the checked
program is the loaded one (`loadsTyped_of_denotesTyped`): `Api.typeOf` checks the program after
expanding its layer references (`Program/Typing.lean:61-64`) while `loadR` loads the program as
written (`RuntimeR.lean:41-46`), so the reduction is for a program with no reference sites. -/

/-- `MachineLive` holds on a running machine whose fibers carry the empty context and whose
store owes nothing. -/
theorem machineLive_of_quiet (m : RState) (stuck : m.stuck = none)
    (contexts : ∀ f ∈ m.fibers, f.context = emptyCtx) (due : m.state.deferreds.due = []) :
    MachineLive m := by
  refine ⟨stuck, fun f hf scope ambient => ?_, fun o ho => ?_⟩
  · rw [contexts f hf] at ambient
    cases ambient
  · rw [due] at ho
    cases ho

/-- **M5's builder.** A root whose loaded code is typed at every world, and whose head is not a
race marker, loads into `J` at the initial world. -/
theorem machineTyped_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (closed : ClosedEff rootTy)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none)
    (code : ∀ w, TypedProg root w rootTy (denoteR root.program root.program (rootPoint compileFuel))) :
    MachineTyped root rootTy (initialWorld rootTy) (loadR root.program fuel compileFuel) := by
  have declared : (initialWorld rootTy).Γ Api.root = some rootTy :=
    insert_here (fun _ : FiberId => (none : Option EffTy)) Api.root rootTy
  refine ⟨⟨initial_world_valid _ root.program fuel compileFuel closed, ⟨?_, ?_, ?_⟩, ?_,
    schedulerState_load root.program fuel compileFuel,
    observerState_load root _ fuel compileFuel,
    registrationState_load root _ fuel compileFuel noMarker⟩, ?_,
    machineLive_of_quiet _ rfl (fun f hf => ?_) rfl⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty hty
      change (initialWorld rootTy).Γ Api.root = some ty at hty
      rw [declared] at hty
      cases hty
      exact savedPosition_of_saved root _ rootTy _
        ⟨rootTy, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro race hr
    cases hr
  · exact ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq
  · intro f hf _ _ _ ty hty
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    change (initialWorld rootTy).Γ Api.root = some ty at hty
    rw [declared] at hty
    cases hty
    exact ⟨rootTy, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
  · change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    rfl

/-- The empty environment is typed at every world. -/
theorem envTyped_nil (w : World) : EnvTyped w [] [] := by
  refine ⟨rfl, fun i ty v h _ => ?_⟩
  rw [List.getElem?_nil] at h
  cases h

/-- **M5 from row 148's fundamental property**, for a program with no layer-reference sites and
a loaded head that is not a race marker (`InterpR.lean:320`: only a race park builds one). -/
theorem loadsTyped_of_denotesTyped (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (denotes : DenotesTyped root) (refFree : root.program.refSites [] = [])
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none) :
    LoadsTyped root rootTy fuel compileFuel := by
  intro _ checked closed
  have expanded : root.program.expandRefs = root.program :=
    expandRefs_eq_self_of_refSites_nil root.program refFree
  have formed : root.program.layerRefsWF = true := layerRefsWF_of_refSites_nil root.program refFree
  have typed : effTy (nativeSignature root.table) [] root.program = some rootTy := by
    change Program.typeOfProgram (nativeSignature root.table) root.program = some rootTy at checked
    unfold Program.typeOfProgram at checked
    rw [expanded, formed, refFree] at checked
    exact checked
  exact ⟨initialWorld rootTy, machineTyped_load root rootTy fuel compileFuel closed noMarker
    fun w => denotes w (rootPoint compileFuel) root.program rootTy rfl
      ⟨root.program, [], rfl, Conform.Effect4.Typing.effTy_ok typed _, envTyped_nil w⟩⟩

/-! ## Stack monotonicity (decisions row 135)

Declared until seat B's Kripke closure lands (`M3bWorld` in `Typed/Residual.lean`). At these
definitions both are false (`E4-TYPED-CE-012`): `FrameAccepts`'s `run`/`skip` arms and its hook
premises read the one world the stack is checked at, and the algebra pass's `stackAccepts_not_mono`
(`docs/research/2026-10-01-formal-pass/algebra/probes/P2KripkeTyping.lean:248`, proved with
`FitsExit` for the exit judgment) exhibits an `answer` frame accepted at a world and refused at a
later one. A step that grows the world (an allocation, a fork) keeps every other fiber's saved
stack only through them. -/

def StackMono (root : ProgramSource) : Prop :=
  ∀ (w w' : World) (tin tout : EffTy) (stack : List ScopeFrame), w.leHost w' →
    StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin tout stack →
      StackAccepts (TypedProg root) ExitOk (frameProtocols root) w' tin tout stack

def SavedMono (root : ProgramSource) : Prop :=
  ∀ (w w' : World) (final : EffTy) (saved : RSaved), w.leHost w' →
    Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final saved →
      Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w' final saved

/-- The saved half from the stack half and `M3bWorld.typedProg_mono`'s proposition. -/
theorem savedMono_of_stackMono (root : ProgramSource)
    (programs : ∀ (w w' : World) (ty : EffTy) (p : RProgram), w.leHost w' →
      TypedProg root w ty p → TypedProg root w' ty p)
    (stacks : StackMono root) : SavedMono root := by
  intro w w' final saved ordered typed
  obtain ⟨tin, code, stack, provenance⟩ := typed
  exact ⟨tin, programs w w' tin saved.current ordered code,
    stacks w w' tin final saved.stack ordered stack, provenance⟩

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

/-! ## The decision edits and the fire snapshot (decisions row 140; R3)

`DecisionLift`'s thirteen fields (`Laws/Machine/Lift.lean:308-355`) at `J`, `I`, `O` and the
admission `AnswerOk`: `step` is the eighteen command obligations
(`guarded_stepKeeps_of_stepPreserves`); the other twelve are the edits a decision makes outside the
command loop and the snapshot's bookkeeping, the lift seat's `M6Edits`
(`docs/research/2026-09-30-pass/lift/Lift.lean:849-871`) restated over the split. Six are proved
here (`edit_nil`, `edit_evaluate`, `edit_ran`, `edit_task`, `edit_skip`, `edit_middleware`); six
are declared (`drain`, `yield`, `interrupt`, the two clock steps, `answer`).
`decisionLift_of_ledger` assembles the lift and `decisionKeeps_of_ledger` gives
`decision_preserves`'s proposition by `stepDecisionState_lift`. -/

/-- The empty residue is a typed queue. -/
theorem queueOk_nil (root : ProgramSource) (w : World) (m : RState) : QueueOk root w m [] :=
  { payload := fun _ h => (nomatch h), authority := fun _ h => (nomatch h),
    delivery := fun _ h => (nomatch h), owners := List.nodup_nil, registration := trivial,
    keys := ⟨fun _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩,
    observer := fun _ _ _ h => (nomatch h), enroll := fun _ _ h => (nomatch h),
    noRaceAfterInterrupt := fun _ _ _ h => (nomatch h), links := fun _ _ _ _ _ h => (nomatch h) }

/-- A task's commands read no code. -/
theorem not_readsCode_taskCmds (t : RTask) (id : FiberId) : ¬ ReadsCode id (taskCmds t) := by
  rintro ⟨yielding, member | member⟩ <;> cases t <;>
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member

def EditNil (root : ProgramSource) : Prop := ∀ w m, SnapshotTyped root w m []

def EditEvaluate (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w m id, MachineTyped root rootTy w m → m.stuck = none →
    ConfigTyped root rootTy w m [Cmd.evaluate id, Cmd.drainDue]

def EditDrain (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) owner (f : RFiber), MachineTyped root rootTy w m → m.fiber? owner = some f →
    MachineTyped root rootTy w
        ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) ∧
      SnapshotTyped root w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
        (f.dispatcher.drain).1

def EditRan (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) owner (t : RTask), MachineTyped root rootTy w m →
    MachineTyped root rootTy w (m.emit [RunEvent.ranTask owner t])

def EditTask (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) owner (t : RTask) ts, MachineTyped root rootTy w m → m.stuck = none →
    SnapshotTyped root w m (t :: ts) →
      ConfigTyped root rootTy w (m.emit [RunEvent.ranTask owner t]) (taskCmds t) ∧
        SnapshotTyped root w (m.emit [RunEvent.ranTask owner t]) ts

def EditSkip (root : ProgramSource) : Prop :=
  ∀ w (m : RState) (t : RTask) ts, SnapshotTyped root w m (t :: ts) → SnapshotTyped root w m ts

def EditYield (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) id (v : Bool), MachineTyped root rootTy w m →
    MachineTyped root rootTy w (m.modify id fun f => { f with yieldOverride := some v })

def EditInterrupt (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) who extra target (t : RFiber), MachineTyped root rootTy w m →
    m.fiber? target = some t →
      MachineTyped root rootTy w
        (letI := termEvaluatorFor root.program
         Machine.Lift.interruptEdit (interpR root.program) m who extra target t)

def EditMiddleware (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState), MachineTyped root rootTy w m →
    MachineTyped root rootTy w { m with middlewareInstalled := true }

def EditClockNone (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) millis st, MachineTyped root rootTy w m → m.stuck = none →
    (interpR root.program).clockStep millis m.state = (none, st) →
      ∃ w', w.leHost w' ∧ MachineTyped root rootTy w' { m with state := st }

def EditClockSome (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) millis owed st, MachineTyped root rootTy w m → m.stuck = none →
    (interpR root.program).clockStep millis m.state = (some owed, st) →
      ∃ w', w.leHost w' ∧ MachineTyped root rootTy w' (drainOwed { m with state := st } [owed]).1 ∧
        ((drainOwed { m with state := st } [owed]).1.stuck = none →
          ConfigTyped root rootTy w' (drainOwed { m with state := st } [owed]).1
            ((drainOwed { m with state := st } [owed]).2 ++ [Cmd.drainDue]))

def EditAnswer (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ w (m : RState) id token answer, MachineTyped root rootTy w m → m.stuck = none →
    AnswerOk w m (.answerAsync id token answer) →
      ∃ w', w.leHost w' ∧
        (letI := termEvaluatorFor root.program
         Machine.Lift.Guarded (MachineTyped root rootTy) (ConfigTyped root rootTy)
           (SnapshotTyped root) [] w'
           (driveStep (interpR root.program)
             { m with state := (prepareAsyncAnswer (interpR root.program) m id token answer).1 }
             (.resume id token (prepareAsyncAnswer (interpR root.program) m id token answer).2)
             [Cmd.drainDue]).1
           (driveStep (interpR root.program)
             { m with state := (prepareAsyncAnswer (interpR root.program) m id token answer).1 }
             (.resume id token (prepareAsyncAnswer (interpR root.program) m id token answer).2)
             [Cmd.drainDue]).2)

/-- The six edits with real content: a store or fiber edit outside the command loop. -/
structure DecisionEdits (root : ProgramSource) (rootTy : EffTy) : Prop where
  drain : EditDrain root rootTy
  yield : EditYield root rootTy
  interrupt : EditInterrupt root rootTy
  clockNone : EditClockNone root rootTy
  clockSome : EditClockSome root rootTy
  answer : EditAnswer root rootTy

theorem edit_nil (root : ProgramSource) : EditNil root := fun w m => queueOk_nil root w m

theorem edit_evaluate (root : ProgramSource) (rootTy : EffTy) : EditEvaluate root rootTy :=
  fun w m id typed _ => evaluate_entry root rootTy w m id typed

theorem edit_ran (root : ProgramSource) (rootTy : EffTy) : EditRan root rootTy :=
  fun _ m owner t typed => machineTyped_congr (m := m) (m' := m.emit [RunEvent.ranTask owner t])
    rfl rfl rfl rfl rfl rfl rfl typed

theorem edit_middleware (root : ProgramSource) (rootTy : EffTy) : EditMiddleware root rootTy :=
  fun _ m typed => machineTyped_congr (m := m) (m' := { m with middlewareInstalled := true })
    rfl rfl rfl rfl rfl rfl rfl typed

theorem edit_skip (root : ProgramSource) : EditSkip root := by
  intro w m t ts snapshot
  unfold SnapshotTyped at snapshot
  rw [List.flatMap_cons] at snapshot
  exact (queueOk_append_tasks (commands := taskCmds t) (tasks := ts) |>.mp snapshot).2

theorem edit_task (root : ProgramSource) (rootTy : EffTy) : EditTask root rootTy := by
  intro w m owner t ts typed _ snapshot
  unfold SnapshotTyped at snapshot
  rw [List.flatMap_cons] at snapshot
  obtain ⟨queue, rest⟩ := queueOk_append_tasks (commands := taskCmds t) (tasks := ts) |>.mp snapshot
  exact ⟨⟨edit_ran root rootTy w m owner t typed,
      fun f _ _ reads => absurd reads (not_readsCode_taskCmds t f.id), queueOk_emit _ queue⟩,
    queueOk_emit _ rest⟩

/-- **The decision lift from the ledger.** The eighteen command facts and the six declared edits
give `DecisionLift` at `J`, `I`, `O` and `AnswerOk`; the other six fields are proved here. -/
theorem decisionLift_of_ledger (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command) (edits : DecisionEdits root rootTy) :
    letI := termEvaluatorFor root.program
    Machine.Lift.DecisionLift hostOrder (interpR root.program) (MachineTyped root rootTy)
      (ConfigTyped root rootTy) (SnapshotTyped root) (fun w m d => AnswerOk w m d) :=
  letI := termEvaluatorFor root.program
  { step := guarded_stepKeeps_of_stepPreserves root rootTy steps
    nil := edit_nil root
    evaluate := edit_evaluate root rootTy
    drain := edits.drain
    ran := edit_ran root rootTy
    task := edit_task root rootTy
    skip := edit_skip root
    yield := edits.yield
    interrupt := edits.interrupt
    middleware := edit_middleware root rootTy
    clockNone := edits.clockNone
    clockSome := edits.clockSome
    answer := edits.answer }

/-- **M6b from the eighteen command facts and the six edits**, by `stepDecisionState_lift`. -/
theorem decisionKeeps_of_ledger (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (d : Api.Decision) (steps : ∀ command, StepPreserves root rootTy command)
    (edits : DecisionEdits root rootTy) : DecisionKeeps root rootTy fuel d := by
  intro w m typed admitted
  letI := termEvaluatorFor root.program
  exact Machine.Lift.stepDecisionState_lift (decisionLift_of_ledger root rootTy steps edits) fuel
    w m d typed admitted

/-- The split's re-establishment (decisions row 140): `J` after each command from `I` before it.
`I` contains `J`, so it is the command facts' projection. -/
def Reestablishes (root : ProgramSource) (rootTy : EffTy) : Prop :=
  (∀ command, StepPreserves root rootTy command) →
    ∀ command w m rest, m.stuck = none → ConfigTyped root rootTy w m (command :: rest) →
      ∃ w', w.leHost w' ∧ MachineTyped root rootTy w'
        (letI := termEvaluatorFor root.program
         driveStep (interpR root.program) m command rest).1

theorem reestablishes (root : ProgramSource) (rootTy : EffTy) : Reestablishes root rootTy := by
  intro steps command w m rest running typed
  obtain ⟨w', ordered, after⟩ := steps command w m rest running typed
  exact ⟨w', ordered, after.machine⟩

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

/-- Organization M4 (decisions row 139): every recorded exit's success value names only handles
its machine's stores hold, on every reachable machine. The exit connector from `FitsExit` to the
meaning layer's exit judgment (`organization/verify-ExitOkConnector.lean`, `exitOk_of_fitsExit`)
takes this as its validity premise. It does not follow from `J` while the scope arm of
`HandleFits` checks only the spelling (`organization/verify-ExitOkConnector.lean`'s `redA_scope`)
and `Live` admits scope and memo handles unchecked; with seat A's scope arm and those arms it is a
consequence of `J`, otherwise the native guard's handle facts transport through R4's bridge. -/
def ExitHandlesValid (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) : Prop :=
  LawfulSource root → Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
    RReachable root fuel m →
      ∀ f ∈ m.fibers, ∀ v, f.exit = some (.success v) → Val.validIn m.state v = true

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

/-- Row 148: the fundamental property (algebra A3); wave 2 proves it with `seq_typed`. -/
theorem denoteR_typed (root : ProgramSource) : ProofGraph.Obligation (DenotesTyped root) := ⟨⟩

/-- Row 148: term soundness at `Fits` (types TY-07); seat A proves it. -/
theorem evalTerm_fits (table : RowTable) : ProofGraph.Obligation (TermFits table) := ⟨⟩

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

/-- `E4-TYPED-CE-012` refuted it as declared at `dceae006` (one `loop` allocates a cell and no
world types the result: the saved stack does not transport along world growth,
`docs/research/2026-10-01-landing/ports-at-dceae006/HeadStepLoop.lean`); the split keeps the
saved-stack clause at the world, so the refutation is expected to carry (not re-run here); seat
B's Kripke closure (row 135) is the repair. Its halting arms (the census in `MachineLive`'s
section) need the scope-liveness and target-declaration pres on `fiberPre`'s scope- and
target-reading rows (seat B); the absent-scope callback that refutes `step_deliver` reaches the
same walk from `loop` (`Laws/Program/EvaluateR.lean:309-319`; reading, not checked here). -/
theorem step_loop (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.loop id yielding)) := ⟨⟩

/-- Refuted at this commit by `E4-SCHED-CE-020`'s witness under `J`'s `stuck = none`
(`M6Capstone.H1HaltAmendment.step_deliver_refuted_by_absent_scope`): `fiberPre` admits
`.scopeExit` on an absent scope (`Typed/Residual.lean:132`), so a typed configuration's delivery
halts. Seat B's scope-liveness pre (row 139) is the repair. -/
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
the typed corpus's `awaitFiber.value`; seat B, row 136; restated against `J` in
`Test/Counterexamples/Machine/Semantics/AwaitLoad.lean`, `loadsTyped_false`); either falsifies the
capstone at the loaded machine. `E4-TYPED-CE-011` (the saved-code clause read at a budget cut) refuted the
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

/-- Scope-handle validity (organization M4, row 139): recorded exits name only live handles on
every reachable machine; the exit connector's premise. -/
theorem exitHandles_valid (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ProofGraph.Obligation (ExitHandlesValid root rootTy fuel m) := ⟨⟩

end M7

/-! The decision edits and the fire snapshot (decisions row 140, R3): `DecisionLift`'s fields
other than `step`, over `J`, `I` and `O`, and the split's re-establishment. -/
namespace M6Edits

theorem nil (root : ProgramSource) : ProofGraph.Obligation (EditNil root) := ⟨⟩
theorem evaluate (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditEvaluate root rootTy) := ⟨⟩
theorem drain (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditDrain root rootTy) := ⟨⟩
theorem ran (root : ProgramSource) (rootTy : EffTy) : ProofGraph.Obligation (EditRan root rootTy) := ⟨⟩
theorem task (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditTask root rootTy) := ⟨⟩
theorem skip (root : ProgramSource) : ProofGraph.Obligation (EditSkip root) := ⟨⟩
theorem yield (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditYield root rootTy) := ⟨⟩
theorem interrupt (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditInterrupt root rootTy) := ⟨⟩
theorem middleware (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditMiddleware root rootTy) := ⟨⟩
theorem clockNone (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditClockNone root rootTy) := ⟨⟩
theorem clockSome (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditClockSome root rootTy) := ⟨⟩
theorem answer (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (EditAnswer root rootTy) := ⟨⟩
theorem reestablish (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (Reestablishes root rootTy) := ⟨⟩

end M6Edits

/-! Stack monotonicity (decisions row 135), declared here until seat B's `M3bWorld` closes it. -/
namespace M6Stack

theorem stackAccepts_mono (root : ProgramSource) : ProofGraph.Obligation (StackMono root) := ⟨⟩
theorem savedOk_mono (root : ProgramSource) : ProofGraph.Obligation (SavedMono root) := ⟨⟩

end M6Stack

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M3bAssembly.capture_lookup :=
  @Effect4.Program.Typed.capture_lookup
#proof_wanted Effect4.Program.Typed.M3bAssembly.typedState_load
#proof_wanted Effect4.Program.Typed.M3bAssembly.denoteR_typed
#proof_wanted Effect4.Program.Typed.M3bAssembly.evalTerm_fits
#typed_state_obligations Effect4.Program.Typed.M3bAssembly ceiling 3
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
#proof_wanted Effect4.Program.Typed.M7.exitHandles_valid
#typed_state_obligations Effect4.Program.Typed.M7 ceiling 4
  using aesop (rule_sets := [Effect4.TypedState])
#obligation_proved Effect4.Program.Typed.M6Edits.nil := @Effect4.Program.Typed.edit_nil
#obligation_proved Effect4.Program.Typed.M6Edits.evaluate := @Effect4.Program.Typed.edit_evaluate
#obligation_proved Effect4.Program.Typed.M6Edits.ran := @Effect4.Program.Typed.edit_ran
#obligation_proved Effect4.Program.Typed.M6Edits.task := @Effect4.Program.Typed.edit_task
#obligation_proved Effect4.Program.Typed.M6Edits.skip := @Effect4.Program.Typed.edit_skip
#obligation_proved Effect4.Program.Typed.M6Edits.middleware := @Effect4.Program.Typed.edit_middleware
#obligation_proved Effect4.Program.Typed.M6Edits.reestablish := @Effect4.Program.Typed.reestablishes
#proof_wanted Effect4.Program.Typed.M6Edits.drain
#proof_wanted Effect4.Program.Typed.M6Edits.yield
#proof_wanted Effect4.Program.Typed.M6Edits.interrupt
#proof_wanted Effect4.Program.Typed.M6Edits.clockNone
#proof_wanted Effect4.Program.Typed.M6Edits.clockSome
#proof_wanted Effect4.Program.Typed.M6Edits.answer
#typed_state_obligations Effect4.Program.Typed.M6Edits ceiling 6
  using aesop (rule_sets := [Effect4.TypedState])
#proof_wanted Effect4.Program.Typed.M6Stack.stackAccepts_mono
#proof_wanted Effect4.Program.Typed.M6Stack.savedOk_mono
#typed_state_obligations Effect4.Program.Typed.M6Stack ceiling 2
  using aesop (rule_sets := [Effect4.TypedState])
