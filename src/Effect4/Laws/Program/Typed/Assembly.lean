import Effect4.Laws.Program.Typed.Stack
import Effect4.Laws.Machine.Lift
import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Program.Typed.Scheduler
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.Typed.Denotation

/-!
# Laws.Program.Typed.Assembly — the typed state of the reference machine, split at the cut

Slice 5's assembly, split by decisions row 134 (ruled 2026-10-01; the formal pass's G1 and its
verifier's split keyed on `running`). The generated predicate bundle `Preds` is instantiated once
(`preds`), independent of the machine and the queue: it types every stored value, exit, stack and
payload position. Current code is typed by two hand clauses keyed on the fiber's own flags and on
the queue, because whether a fiber's code is read again depends on them, not on the saved frame:

* `MachineTyped` (`J`, machine-only and cut-tolerant): world validity, the generated predicate
  with the correlations (`TypedState`), the world's service table tied to the source's (row 112),
  the code of every fiber that has not exited and is not running (`LiveCode`), and
  `stuck = none` with the liveness clauses of row 139 (`MachineLive`).
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
(`M6Edits`: `DecisionLift`'s fields other than `step`, and the split's re-establishment), world
monotonicity (`M3bWorld`: seat B's laws in `Typed/Residual.lean`, with the bundle's `SavedOk`
transport proved and declared here, `preds_savedOk_mono`) and M7 (`M7`: a–c and scope-handle
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
heap table. The declared cell type is compared in the checker's order (decisions row 137,
`Ty.subN`, as `CompletionOk.ofRefGet` and `storePre`'s `deferredCompleteWith` arm read it). -/
def CompletionStrong (w : World) (ty : EffTy) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit ex => ExitOk w ty ex
  | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ Ty.subN t ty.answer = true

/-- The saved stack and its provenance at a position: the stack composes from some intermediate
type to the position's declared type (`PositionStack`: up to row 188 (b)'s injected registration
callback), and recorded causes are interrupts. Current code is not part of it: `LiveCode` and
`ReadCode` type it where it is read. -/
def SavedPosition (root : ProgramSource) (w : World) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, PositionStack root w tin final saved.stack ∧ InterruptProvenance saved

/-- **The promise-table column** (`Typed/Vocabulary.lean`: `Π` declares every Deferred cell at the
type it was made at), its two rows: the work a store owes fits its waiter's token (`Owed`, the due
list), and a memo entry's cell is declared at its layer's columns (the `memoBuild` row, decisions
row 187 (c); `MemoTableTyped`), which `memoGet` and `memoComplete` read (`StoreTyped`). It reads
the two fields it types, so a store edit that keeps them keeps it by computation. -/
structure PromiseTableOk (root : ProgramSource) (w : World)
    (owed : List (Owed (Completion Val Err Defect FiberId Ann))) (memoWorld : MemoWorld) : Prop where
  due : ∀ o ∈ owed, ∀ ty, w.Θ o.waiter o.token = some ty → CompletionStrong w ty o.code
  memo : MemoTableTyped root w memoWorld

/-- The generated bundle, instantiated with the strong judgments once. It depends on neither the
machine nor the queue, so a step that leaves a field alone leaves its clause alone. A closed
scope's exit fits DI-94's release type `Exit<unknown, unknown>` (decisions row 140): its values
are live, `Fits`' `unknown` arm. Every finalizer an open scope holds is typed at rc.112's
finalizer type `⟨unknown, never⟩` at every closing exit of that type (decisions row 151 (a″),
`FinalizerTyped`; the registration pre admits it, `finalizerTyped_of_admitted`). -/
def preds (root : ProgramSource) : Preds World where
  SavedOk w e x := ∀ ty, expectOf w e = some ty → SavedPosition root w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → ExitOk w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProg root) w target token code
  ServiceOk w _ ctx := ServicesFit w ctx.services
  RaceOk w _ races := ∀ r ∈ races, ∃ resultTy, RacePayload root w r resultTy
  PromiseTable w s := PromiseTableOk root w s.deferreds.due s.memo
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → Fits w v ty
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c
  FinalizerOk w _ fin := FinalizerTyped root w fin
  CaptureOk w _ c := CaptureTyped root w c
  ScopeExitOk w _ ex := Fits w (reifyExitVal ex) (.exitOf .unknown .unknown)

/-- A fully typed saved frame, code included, gives its saved position. -/
theorem savedPosition_of_saved (root : ProgramSource) (w : World) (final : EffTy) (saved : RSaved)
    (typed : Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final saved) :
    SavedPosition root w final saved := by
  obtain ⟨tin, _, stack, provenance⟩ := typed
  exact ⟨tin, positionStack_of_stackAccepts stack, provenance⟩

/-- The active park and saved stack agree on what the declared token delivers; the stack may hold
row 188 (b)'s injected registration callback (`HostStack`). -/
def ActiveDelivery (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      HostStack root w m f.id tin final f.frame.stack ∧ InterruptProvenance f.frame

/-- `ActiveDelivery` moves to a machine with the same fibers whose races keep their host and
token (row 188 (b)'s registration arrows read them). -/
theorem activeDelivery_races {root : ProgramSource} {w : World} {m m' : RState}
    (fibers : m'.fibers = m.fibers) (kept : RacesKept m m') (h : ActiveDelivery root w m) :
    ActiveDelivery root w m' := by
  intro f hf token parked
  obtain ⟨tin, final, declared, final', stack, provenance⟩ :=
    h f (by rw [← fibers]; exact hf) token parked
  exact ⟨tin, final, declared, final', hostStack_races kept stack, provenance⟩

/-- `RegistrationState` moves likewise. -/
theorem registrationState_races {root : ProgramSource} {w : World} {m m' : RState}
    (fibers : m'.fibers = m.fibers) (kept : RacesKept m m') (h : RegistrationState root w m) :
    RegistrationState root w m' := by
  intro fiber hf raceId marker
  obtain ⟨race, resultTy, found, host, token, reply⟩ :=
    h fiber (by rw [← fibers]; exact hf) raceId marker
  obtain ⟨race', found', host', token'⟩ := kept raceId race found
  exact ⟨race', resultTy, found', host'.trans host, by rw [host', token']; exact token,
    stackReply_races kept reply⟩

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
  /-- A queued observer types what it can deliver (`ObserverCommandOk`), and its source is a fiber
  id below `nextId` (decisions row 189, `E4-TYPED-CE-035`): the payload clause reads the
  source's declaration antitonically, so a future id's clause would hold vacuously until an
  allocation declared it. Missing old sources stay inert. -/
  observer : ∀ source exit observer, .observe source exit observer ∈ commands →
    source.value < m.nextId ∧ ObserverCommandOk root w m source exit observer
  enroll : ∀ race child, .enrollRace race child ∈ commands → EnrollRaceOk root w m race child
  noRaceAfterInterrupt : ∀ host yielding race,
    .afterInterrupt host yielding (.race race) ∉ commands
  /-- A queued `link` names a scope the store holds (`Stores.ScopeLive`, row 156's predicate at
  the machine's store) and an existing target: `linkScope` halts otherwise
  (`Machine/Fibers.lean:1005-1036`). Row 139's typed scope on a queued link. -/
  links : ∀ mode scope target interruptor extra,
    .link mode scope target interruptor extra ∈ commands →
      m.state.ScopeLive scope ∧ (m.fiber? target).isSome = true
  /-- Decisions row 134 (d), on the queue: a queued observer holds no race's key. A stored observer
  is queued when its fiber exits (`finish`) and the countdown walk re-stores a queued one
  (`observe`), so the stored clause (`SchedulerState.raceObservers`) is kept only with this one. -/
  raceObservers : ∀ source exit o, .observe source exit o ∈ commands → ∀ raceId race,
    m.race? raceId = some race → (race.host, race.token) ∉ Guard.observerKeys o

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
`RegistrationState`'s; a registration callback an injected yield saved in the stack is a
registration arrow of the code's `HostStack` (decisions row 188 (b)). -/
def LiveCode (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → f.running = false → raceRegistrationR f.frame.current = none →
    f.parked = .notParked → ∀ ty, w.Γ f.id = some ty → CodeOk root w m f.id ty f.frame

/-- `I`'s code clause for running fibers: a running fiber whose current code a queued `loop` or
`deliver` reads is typed with its stack at its declared type. A running fiber continued by
`finish`, the race commands or the interrupt commands is typed by their own facts (`QueueOk`,
`RegistrationState`; the module header's table); one that no queued command continues is
inert. -/
def ReadCode (root : ProgramSource) (w : World) (m : RState) (commands : List RCmd) : Prop :=
  ∀ f ∈ m.fibers, f.running = true → ReadsCode f.id commands →
    raceRegistrationR f.frame.current = none → ∀ ty, w.Γ f.id = some ty →
      CodeOk root w m f.id ty f.frame

/-- `ReadCode` moves to a machine with the same fibers whose races keep their host and token. -/
theorem readCode_races {root : ProgramSource} {w : World} {m m' : RState} {q : List RCmd}
    (fibers : m'.fibers = m.fibers) (kept : RacesKept m m') (code : ReadCode root w m q) :
    ReadCode root w m' q := by
  intro f hf running reads marker ty declared
  exact codeOk_races kept (code f (by rw [← fibers]; exact hf) running reads marker ty declared)

/-- Row 139's halting freedom and liveness, on the machine alone. Each clause names the halting
arm it rules out; with the scope-finalizer drops of `ObserverState` and `QueueOk.observer`, with
`QueueOk.links` (in `I`) and the target and scope premises on the halting fiber rows (`fiberPre`'s
`interruptAs`, `runIn`, `forkIn`, `closeScope`, `scopeExit` arms; `raceRegister` refused) they are
what each command proof needs to show its halting arms unreachable. The scope-exit marker is
typed only at the run position of the guard the `scoped` arm installs and of the slot that guard
saves (`TypedProg.scopedGuard`, `FrameAccepts.scopedResume`, decisions row 188 (a)), which carry the
same presence (`ScopeLive`, row 156) that `fiberPre`'s `scopeExit` arm states. Race-id liveness for the
codes that name a race is `RegistrationState` (in `TypedState`): the only race halt is
`registerRace` on a registration marker (`Machine/Fibers.lean:937-944`), and both code clauses
leave the marker to it. A fiber handle's liveness is `Fits`'s fiber arm with
`WorldValid.fibers`; a fiber context's ambient scope is present by membership (`forkScoped` links
the child into it, `:1474-1489`, `linkScope` `:1005-1036`): `ambientScope_live`, from `J`'s typed
state, which replaced this structure's stand-in field `ambientScopes` at decisions row 156. -/
structure MachineLive (m : RState) : Prop where
  /-- The machine has not halted (`E4-TYPED-CE-014`): every halting arm of a command is an
  obligation of that command's preservation proof. -/
  running : m.stuck = none
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
  /-- The world's static service table is the source's (decisions row 112, shape A): the world
  order fixes the table (`le_serviceTy`), so the tie holds along every run once it holds at the
  load (`initialWorld rootTy root.sig.serviceTy`), and `ServicesFit` reads the source's carriers. -/
  services : w.serviceTy = root.sig.serviceTy
  code : LiveCode root w m
  live : MachineLive m
  /-- The source's layer references are well formed (decisions row 170): a constant fact of the
  source, carried so a step that creates code from a point reads M5's `DenotesTyped`, whose premise
  it is (without it a fork of a checked point that denotes `badShapeExit` breaks the step,
  `E4-TYPED-CE-020`'s shape). The load discharges it from the checker's verdict
  (`layerRefsWF_of_typeOf`); every step keeps it. A field of `J`, not of `ProgramSource`. -/
  sourceWF : root.program.layerRefsWF = true

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

/-- **Every fiber's ambient scope is present** (decisions rows 139 and 156), from `J`: the
fiber context's services fit their keys' carriers (`preds`' `ServiceOk`), the world's service
table is the source's (row 112), which types the reserved `Scope` key at `Ty.scope`, and a scope
handle's membership reads its scope's presence (row 156). With `WorldValid.state` it is the
machine's store: `forkScoped`'s link never halts on the ambient scope (`Machine/Fibers.lean`
`:1474-1489`, `linkScope` `:1005-1036`). It replaced `MachineLive`'s stand-in field. -/
theorem ambientScope_live {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) {f : RFiber} (hf : f ∈ m.fibers) {scope : Nat}
    (ambient : Ctx.ambientScope f.context = some scope) : ScopeLive w scope := by
  obtain ⟨⟨_, ok, _, _, _, _⟩, services, _, _⟩ := typed
  have fit : ServicesFit w f.context.services := (ok.c0 f hf).c5
  have bound : f.context.services.getV Env.scopeKey = some (Val.scopeHandle scope) := by
    change Env.scopeOfVal (f.context.services.getV Env.scopeKey) = some scope at ambient
    unfold Env.scopeOfVal at ambient
    split at ambient
    · rename_i sc hsc
      cases ambient
      exact hsc
    · cases ambient
  have carrier : w.serviceTy Env.scopeKey = some Ty.scope := by
    rw [services]
    rfl
  exact (fit.1 Env.scopeKey _ _ bound carrier).2

/-- **The ambient-scope read answers inside its post at `J`** (decisions row 156): the machine
answers `.ambientScope` with the fiber context's ambient scope (`FiberAction.ambientScope`,
`Machine/Fibers.lean:1491-1498`), which `J` holds present (`ambientScope_live`), so the handle
fits `Ty.scope` (`ambientScope_answers`). -/
theorem ambientScope_answers_of_typed {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} (typed : MachineTyped root rootTy w m) {f : RFiber} (hf : f ∈ m.fibers)
    {scope : Nat} (ambient : Ctx.ambientScope f.context = some scope) :
    fiberPost w .ambientScope () ((interpR root.program).scopeValue scope) :=
  ambientScope_answers root w scope (ambientScope_live typed hf ambient)

/-- A halted machine is outside `J` (row 139; probe C's `typedState_halt`, read at `J`). -/
theorem machineTyped_not_halted (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (why : Stuck) : ¬ MachineTyped root rootTy w (m.halt why) := by
  intro typed
  have running : (m.halt why).stuck = none := typed.live.running
  cases running

/-- **`J` types the store the store rows read** (seat B's `StoreTyped`, `Typed/Adequacy.lean`;
receipt-B "For seat C" item 3): the declarations cover exactly the allocated cells and promises
(`WorldValid.heap`, `.promises` over `WorldValid.state`), every stored value fits its cell's
declared type (the generated `HeapCell` column), and every closing exit a scope holds fits
`Exit<unknown, unknown>` (the un-refused `ScopeExitOk` row, row 140), every memo entry's
allocations exist (`WorldValid.wf`'s memo clause, which `memoRelease`'s post reads, row 156), and
every memo entry's cell is declared at its layer's columns (the promise table's memo row,
`PromiseTableOk.memo`, row 187). It reads only `J`'s `TypedState`; `storeStep_typed` consumes it
in wave 2's `loop` arm. -/
theorem storeTyped_of_typedState {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} (typed : MachineTyped root rootTy w m) : StoreTyped root w := by
  obtain ⟨⟨valid, ok, _, _, _, _⟩, _, _, _⟩ := typed
  refine ⟨fun key => ?_, fun key => ?_, fun i v hv ty hty => ?_, fun e he ex hex => ?_, ?_, ?_⟩
  · rw [valid.state]
    exact valid.heap key
  · rw [valid.state]
    exact valid.promises key
  · rw [valid.state] at hv
    exact ok.c2.c1 i v hv ty hty
  · rw [valid.state] at he
    have entry : ScopeStateOk (preds root) w Expect.root e.scope.state := (ok.c2.c3.c0 e he).c0.c0
    change e.scope.state.closingExit? = some ex at hex
    generalize e.scope.state = state at entry hex
    cases state with
    | closed exit =>
      cases hex
      exact entry
    | empty => cases hex
    | openEmpty => cases hex
    | openInline _ _ => cases hex
    | openMap _ => cases hex
  · rw [valid.state]
    exact valid.wf.2.2.1
  · rw [valid.state]
    exact PromiseTableOk.memo ok.c2.c0

/-- **The generated scope clause types every finalizer the scope holds** (decisions row 151
(a″)): it states the bundle's `FinalizerOk` at the inline slot and at each entry of the map, and a
scope's close order is its registrations, backwards (`Effect4.Scope.closeOrder_eq`). -/
theorem scopeFinalizers_typed {root : ProgramSource} {w : World} {e : Expect} {sc : ScopeV}
    (h : ScopeStateOk (preds root) w e sc.state) :
    ∀ fin ∈ sc.closeOrder, FinalizerTyped root w fin := by
  intro fin hfin
  rw [Effect4.Scope.closeOrder_eq, List.mem_reverse] at hfin
  obtain ⟨⟨key, fin'⟩, hmem, hfin'⟩ := List.mem_map.mp hfin
  subst hfin'
  rw [Effect4.Scope.finalizers_eq] at hmem
  generalize sc.state = state at h hmem
  cases state with
  | openInline k f =>
    rw [ScopeState.entries_openInline, List.mem_singleton] at hmem
    cases hmem
    exact h.1
  | openMap entries =>
    rw [ScopeState.entries_openMap] at hmem
    exact h.1 (key, fin') hmem
  | empty => cases hmem
  | openEmpty => cases hmem
  | closed _ => cases hmem

/-- **`J` types every finalizer a scope of the world's store holds** (decisions row 151 (a″)), the
store typing `closeScope_installs` reads at a close. -/
theorem finalizers_of_typedState {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} (typed : MachineTyped root rootTy w m) :
    ∀ entry ∈ w.state.scopes.entries, ∀ fin ∈ entry.scope.closeOrder, FinalizerTyped root w fin := by
  obtain ⟨⟨valid, ok, _, _, _, _⟩, _, _, _⟩ := typed
  intro entry he
  rw [valid.state] at he
  exact scopeFinalizers_typed (ok.c2.c3.c0 entry he).c0.c0

/-- **TY-08's promise half (proved)**: the coarse promise column (`PromiseTable`, the leaf
`CompletionOk`) from the strong one (`preds`' `PromiseCell`, the leaf `CompletionStrong`): an
exit through `completionOk_of_fitsExit`, a reference completion as it stands (both read the cell's
declaration in `Ty.subN`, row 137). The heap half is `heapTable_of_fits` (`Membership.lean`). -/
theorem promiseTable_of_strong {w : World}
    (h : Columns.DeferredStore_cells (fun w key cell => ∀ a e, w.«Π» key = some (a, e) →
      ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c) w
      w.state.deferreds.cells) : PromiseTable w := by
  intro i cell hc types hty c hcomp
  obtain ⟨a, e⟩ := types
  have strong := h i cell hc a e hty c hcomp
  cases c with
  | ofExit ex => exact completionOk_of_fitsExit strong.1
  | ofRefGet _ => exact strong

/-- **TY-08 (proved)**: the generated typed state gives the coarse cell columns `WorldValid.cells`
states, from its strong heap and promise columns. So that field is redundant beside the typed
state (dropping it from `WorldValid` is owed: every construction of `WorldValid` builds it). -/
theorem cells_of_typedState {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : TypedState root rootTy w m) : HeapTable w ∧ PromiseTable w := by
  obtain ⟨valid, ok, _, _, _, _⟩ := typed
  refine ⟨heapTable_of_fits fun i v hv ty hty => ?_, promiseTable_of_strong fun i cell hc => ?_⟩
  · rw [valid.state] at hv
    exact ok.c2.c1 i v hv ty hty
  · rw [valid.state] at hc
    exact ok.c2.c2.c0 i cell hc

/-- **The loop-entry premise holds for this split** (`DecisionLift.evaluate`): `J` gives `I` at
the fresh queue an evaluate or interrupt decision starts, at every machine, a budget cut
included. The proofs seat's split keyed on a queued `finish` fails exactly here
(`Test/Counterexamples/Machine/Semantics/StaleCode.lean`, `seat_split_not_decisionLift`). -/
theorem evaluate_entry (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (id : FiberId) (typed : MachineTyped root rootTy w m) :
    ConfigTyped root rootTy w m [Cmd.evaluate id, Cmd.drainDue] := by
  refine ⟨typed, ?_, ⟨?_, ?_, ?_, List.nodup_nil, ⟨trivial, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_,
    ?_⟩⟩
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
  · intro source exit observer member
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
        fun md sc tg ir ex hl => queue.links md sc tg ir ex (List.mem_append_left _ hl),
        fun s e o ho => queue.raceObservers s e o (List.mem_append_left _ ho)⟩,
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
        fun md sc tg ir ex hl => queue.links md sc tg ir ex (List.mem_append_right _ hl),
        fun s e o ho => queue.raceObservers s e o (List.mem_append_right _ ho)⟩⟩
  · rintro ⟨queue, snapshot⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, ?_,
      registrationQueue_append_tasks.mpr ⟨queue.registration, snapshot.registration⟩, ⟨?_, ?_⟩,
      fun s e o ho => ?_, fun r c hc => ?_, fun h y r hr => ?_, fun md sc tg ir ex hl => ?_,
      fun s e o ho => ?_⟩
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
    · rcases List.mem_append.mp ho with ho | ho
      · exact queue.raceObservers s e o ho
      · exact snapshot.raceObservers s e o ho

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
  obtain ⟨⟨valid, ok, deliv, sched, obsv, reg⟩, services, code, live, sourceWF⟩ := typed
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
    fun f hf token parked => ?_, ?_,
    ⟨fun f hf => obsv.pendingOwner f (member f hf), fun f hf o ho =>
      storedObserverOk_congr lookup raceLookup state o (obsv.observers f (member f hf) o ho)⟩,
    fun f hf raceId marker => ?_⟩, services, fun f hf hx hr hm hp ty d =>
      codeOk_races (racesKept_of_eq raceLookup) (code f (member f hf) hx hr hm hp ty d), ?_, sourceWF⟩
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
        root := valid.root
        timers := by rw [state]; exact valid.timers
        waiters := by rw [state]; exact valid.waiters
        children := fun f hf => valid.children f (member f hf) }
  · rw [races]
    exact ok.c1
  · rw [state]
    exact ok.c2
  · obtain ⟨tin, final, d1, d2, st, pv⟩ := deliv f (member f hf) token parked
    exact ⟨tin, final, d1, d2, hostStack_races (racesKept_of_eq raceLookup) st, pv⟩
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
        exitedStack := fun f hf => sched.exitedStack f (member f hf)
        deferredCause := fun f hf => sched.deferredCause f (member f hf)
        raceObservers := fun r race hr f hf o ho =>
          sched.raceObservers r race ((raceLookup r).symm.trans hr) f (member f hf) o ho
        liveBelow := fun r race hr id hid => by
          rw [nextId]
          exact sched.liveBelow r race ((raceLookup r).symm.trans hr) id hid
        targetsBelow := fun f hf p hp id hid => by
          rw [nextId]
          exact sched.targetsBelow f (member f hf) p hp id hid
        observersBelow := fun f hf o ho k hk => by
          rw [nextId]
          exact sched.observersBelow f (member f hf) o ho k hk }
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := reg f (member f hf) raceId marker
    exact ⟨race, resultTy, (raceLookup raceId).trans found, host, token,
      stackReply_races (racesKept_of_eq raceLookup) reply⟩
  · refine ⟨stuck.trans live.running, fun o ho owner priority mode => ?_⟩
    rw [state] at ho
    rw [lookup]
    exact live.dueOwners o ho owner priority mode

/-- The queue facts survive a trace edit: an `emit` changes no lookup, counter or store. -/
theorem queueOk_emit {root : ProgramSource} {w : World} {m : RState} {commands : List RCmd}
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit))
    (queue : QueueOk root w m commands) : QueueOk root w (m.emit events) commands :=
  { payload := queue.payload, authority := queue.authority,
    delivery := fun c hc => commandDelivery_mono (m := m) (m' := m.emit events) (leHost_refl w)
      (fun _ _ h => h) (racesKept_of_eq fun _ => rfl) (fun _ _ => rfl) (queue.delivery c hc),
    owners := queue.owners, registration := queue.registration,
    keys := ⟨queue.keys.below, queue.keys.disjoint⟩,
    observer := fun source exit o ho => ⟨(queue.observer source exit o ho).1,
      observerCommandOk_congr (m := m) (m' := m.emit events)
        (fun _ => rfl) (fun _ => rfl) rfl o (queue.observer source exit o ho).2⟩,
    enroll := queue.enroll, noRaceAfterInterrupt := queue.noRaceAfterInterrupt,
    links := queue.links, raceObservers := queue.raceObservers }

/-! ## The capture lookup -/

/-- A capture's release runs at the point its path's `acquireRelease` checks it at — the
release child, over the checker's environment extended by the acquired value and the exit, with
the completed view the release is constructed with (`denoteFin`'s `foreign` arm reads it from the
`construction` post, whose clause `hview` is; decisions row 175) — at a type whose error column
normalizes to `never`: the checker's `acquireRelease` rule refuses a release that can fail
(`Program/Checker.lean:201-209`; rc.112's release is `Effect<unknown, never, R2>`,
`internal/effect.ts:3973`). -/
theorem capture_release (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (h : CaptureTyped root w c)
    (hex : Fits w exVal (.exitOf .unknown .unknown))
    (hview : ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2) :
    ∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty ∧
      rty.error.normalize = .never := by
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, _⟩ := h
  rw [Eff.expandIn_acquireRelease] at hcheck
  obtain ⟨a', r, hacq', hrel, hnever, _⟩ := Checker.inv_acquireRelease _ _ _ _ _ t hcheck
  rw [hacq] at hacq'
  cases hacq'
  refine ⟨r, ⟨release, env ++ [a.answer, .exitOf .unknown .unknown], ?_, hrel, ?_, hview⟩, hnever⟩
  · show Node.at_ (.eff root.program) (c.path ++ [1]) = some (.eff release)
    rw [Agreement.Node.at_append, hnode]
    rfl
  · show EnvTyped w (env ++ [a.answer, .exitOf .unknown .unknown]) (c.env ++ [exVal])
    have := envTyped_append henv hex
    simpa only [List.append_assoc, List.singleton_append] using this

/-- A capture's release runs at the point its path's `acquireRelease` checks it at: the
release child, over the checker's environment extended by the acquired value and the exit, with
the completed view it is constructed with (decisions row 175). -/
theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (h : CaptureTyped root w c)
    (hex : Fits w exVal (.exitOf .unknown .unknown))
    (hview : ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2) :
    ∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty :=
  (capture_release root w c completed exVal h hex hview).imp fun _ typed => typed.1

/-! ## Registered finalizers: from the registration pre to the scope store's typing

Decisions row 151 (a″). The registration pre reads a finalizer's admission by name
(`FinalizerAdmitted`, `Typed/Admission.lean`: the pre is a premise of the program judgment, so it
cannot mention it); the scope store's typing states the program's typing (`FinalizerTyped`,
`Typed/Adequacy.lean`). The bridge is one theorem per finalizer name: the synthetic finalizers by
their programs, the foreign one by its capture's typing. -/

/-- The void answer at rc.112's finalizer type. -/
theorem exitOk_unit_finalizer (w : World) :
    ExitOk w ⟨.unknown, .never, Env.Requirement.empty⟩ (.success .unit) :=
  ⟨(fitsExit_success_iff w _ _).mpr (live_of_handles_nil rfl), trivial⟩

/-- An exit at a type whose error column normalizes to `never` is an exit at the finalizer type
`⟨unknown, never⟩`: the answer column is below `unknown`, the error column below `never`. -/
theorem exitOk_finalizer {w : World} {ty : EffTy} (herr : ty.error.normalize = .never)
    {ex : ExitV} (h : ExitOk w ty ex) : ExitOk w ⟨.unknown, .never, Env.Requirement.empty⟩ ex := by
  have hans : Ty.subN ty.answer .unknown = true := Ty.sub_unknown ty.answer.normalize
  have herr' : Ty.subN ty.error .never = true := by
    show Ty.sub ty.error.normalize Ty.never.normalize = true
    rw [herr]
    exact Ty.sub_refl _
  exact ⟨fitsExit_subN (ty := ty) (ty' := ⟨.unknown, .never, Env.Requirement.empty⟩) hans herr' h.1,
    h.2⟩

/-- **The registration pre gives the scope store's typing** (decisions row 151 (a″)): a finalizer
the registration admits is typed at rc.112's finalizer type `⟨unknown, never⟩` at every later
world and every closing exit that fits `Exit<unknown, unknown>`. The synthetic finalizers by
their programs (a scope they close or detach is present, scope persistence keeping it so); a
foreign one by its capture's typing: the counted suspend, the context read and restore under
their guards, the construction query, and the masked release at the point the checker types it
(`capture_release`), its answer below `unknown` and its error column `never`. -/
theorem finalizerTyped_of_admitted (root : ProgramSource) (w : World) (fin : FinName)
    (h : FinalizerAdmitted root w fin) : FinalizerTyped root w fin := by
  intro w' ord ex hex
  cases fin with
  | interruptFiber fiber skipSelf =>
    have declared : (w'.Γ fiber).isSome = true := isSome_extends ord.1.2.1 h
    cases skipSelf with
    | true =>
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () declared fun w'' _ ans post => ?_
      subst post
      exact TypedProg.pure (exitOk_unit_finalizer w'')
    | false =>
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () declared fun w'' _ ans post => ?_
      subst post
      exact TypedProg.pure (exitOk_unit_finalizer w'')
  | closeChildScope scope =>
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () ⟨scopeLive_mono ord.1 h, hex⟩
      fun _ _ _ post => TypedProg.pure (exitOk_finalizer rfl post)
  | detachFromParent parent key =>
    refine TypedProg.store () (scopeLive_mono ord.1 h) fun w'' _ ans post => ?_
    subst post
    exact TypedProg.pure (exitOk_unit_finalizer w'')
  | release label fails =>
    subst h
    exact TypedProg.pure (exitOk_unit_finalizer w')
  | parkThen slot =>
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (⟨.unknown, .never, Env.Requirement.empty⟩ : EffTy) trivial
      fun _ _ _ post => TypedProg.pure post
  | awaitNewChildren snapshot =>
    refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () trivial fun w'' _ ans post => ?_
    subst post
    exact TypedProg.pure (exitOk_unit_finalizer w'')
  | closeChildOnFailure scope =>
    cases ex with
    | success _ => exact TypedProg.pure (exitOk_unit_finalizer w')
    | failure cause =>
      exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () ⟨scopeLive_mono ord.1 h, hex⟩
        fun _ _ _ post => TypedProg.pure (exitOk_finalizer rfl post)
  | memoDone layer memoMap => exact h.elim
  | memoEntry layer memoMap =>
    -- `observers--` answers `unit` or the layer scope's handle, present (`memoRelease`'s post),
    -- carried through the guard at `unit | Scope`; the last observer closes that scope
    refine seq_typed root (mid := ⟨.union .unit Ty.scope, .never, Env.Requirement.empty⟩) ?_ ?_ rfl
    · refine TypedProg.store () trivial fun w'' _ ans post => TypedProg.pure ⟨?_, trivial⟩
      show Fits w'' ans .unit ∨ Fits w'' ans Ty.scope
      rcases post with unit | scope
      · subst unit
        exact Or.inl trivial
      · exact Or.inr scope
    · intro w'' o'' v hv
      rcases hv with unit | scope
      · rw [fits_unit_inv unit]
        exact TypedProg.pure (exitOk_unit_finalizer w'')
      · obtain ⟨sc, rfl, live⟩ := fits_scope_inv scope
        exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
          (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () ⟨live, fitsExit_mono o'' hex⟩
          fun _ _ _ post => TypedProg.pure (exitOk_finalizer rfl post)
  | foreign c =>
    have hc : CaptureTyped root w' c := finalizerAdmitted_mono root ord (.foreign c) h
    -- the counted suspend before the release
    refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () trivial fun w1 o1 _ _ => ?_
    -- the context read, under its guard
    refine seq_typed root (mid := ⟨.handle Ty.contextTarget, .never, Env.Requirement.empty⟩) ?_ ?_ rfl
    · exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (.handle Ty.contextTarget) rfl
        fun _ _ _ post => TypedProg.pure ⟨post, trivial⟩
    · intro w2 o2 v hv
      obtain ⟨previous, hprev, hprevious⟩ := fits_context_inv hv
      have o12 : w'.leHost w2 := leHost_trans _ _ _ o1 o2
      obtain ⟨_, _, _, _, _, _, _, _, _, hsvc⟩ := finalizerAdmitted_mono root o12 (.foreign c) hc
      show TypedProg root w2 _ (match Val.context? v with
        | some previous =>
          (guardR .onSuccess (fiberValR (.setContext c.ctx) rfl)).bind (seqR fun _ =>
            constructR fun completed =>
              .vis (.inr (.mask false
                (.release ((Point.ofCapture c completed).childWith 1 (reifyExitVal ex)) previous)))
                Effects.Program.pure)
        | none => .pure badShapeExit)
      rw [hprev]
      -- the captured context set, under its guard
      refine seq_typed root (mid := EffTy.pure .unit) ?_ ?_ rfl
      · refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
          (fun _ _ _ h => nomatch h) () hsvc fun w3 _ ans post => ?_
        subst post
        exact TypedProg.pure ⟨trivial, trivial⟩
      · intro w3 o3 _ _
        -- the construction query, then the masked release
        refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
          (fun _ _ _ h => nomatch h) () trivial fun w4 o4 completed hview => ?_
        have o14 : w'.leHost w4 := leHost_trans _ _ _ o12 (leHost_trans _ _ _ o3 o4)
        obtain ⟨rty, hpt, hnever⟩ := capture_release root w4 c completed (reifyExitVal ex)
          (finalizerAdmitted_mono root o14 (.foreign c) hc) (fitsExit_mono o14 hex) hview
        exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
          (fun _ _ _ h => nomatch h) rty
          (.release _ _ rty hpt (servicesFit_mono (leHost_trans _ _ _ o3 o4) hprevious))
          fun _ _ _ post => TypedProg.pure (exitOk_finalizer hnever post)

/-! ## The milestone propositions

Named once, so the ledger's declarations and the connectors below read the same statement. -/

/-- Rows 111–116: the source's Σ_app is lawful, the proposition seat A's evidence field on
`ProgramSource` carries (`ProgramSource.lawful`, row 114), so every source has it
(`root.lawful`) and M5 and M6 quantify over lawful sources. It contains the program-plane
row-table check this premise read before (`Table.lawful`: unique keys, no built-in collision, no
dropped trailing names; `LawfulSig.tableLawful`) and adds the service-table clauses (rows
112–114). The statements keep this premise's name; `w.serviceTy` is tied to the source in
`MachineTyped` (row 112). -/
def LawfulSource (root : ProgramSource) : Prop := LawfulSig root.sig

/-- M5's proposition: a lawful, checked, closed source whose requirement row is empty loads into
`J`. The empty row is rc.112's own rule for a run (decisions row 117, ruled 2026-10-01):
`Effect.runPromise` takes an `Effect<A, E>`, whose requirement parameter is `never`
(`Effect.ts:17494-17497`); an open row runs only through `runPromiseWith(context)`. No proof reads
the premise yet: it is part two's (the presence clause), which stays open. -/
def LoadsTyped (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) : Prop :=
  LawfulSource root → Program.typeOfProgram root.signature root.program = some rootTy →
    rootTy.requires = Env.Requirement.empty →
      ∃ w, MachineTyped root rootTy w (loadR root.program fuel compileFuel)

/-- M6b's proposition: one tape decision keeps `J` when its host answer, if any, is admitted. -/
def DecisionKeeps (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    Prop :=
  ∀ w m, MachineTyped root rootTy w m → AnswerOk w m d →
    ∃ w', w.leHost w' ∧ MachineTyped root rootTy w'
      (letI := termEvaluatorFor root.program
       stepDecisionState (interpR root.program) fuel m d).1

/-- M6c's proposition: every machine an answer-free tape reaches from a lawful, checked, closed
source whose requirement row is empty is in `J` (the empty row as `LoadsTyped` takes it, rc.112's
`runPromise`, `Effect.ts:17494-17497`; decisions row 117). -/
def ReachableTyped (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) : Prop :=
  LawfulSource root → Program.typeOfProgram root.signature root.program = some rootTy →
    rootTy.requires = Env.Requirement.empty → RReachable root fuel m →
      ∃ w, MachineTyped root rootTy w m

/-- Row 148 (algebra A3): M5's fundamental property. For a program whose layer references are
well formed, a checked point denotes, at the node its path names, a program typed at the point's
certificate, at every world whose service table is the source's.

The well-formedness premise is decisions row 170 (`E4-TYPED-CE-020`): `PointTyped` reads a node
through the expansion's rounds (`Eff.expandIn`), which resolve a reference to a reference, while
the run's `.ref` arm answers `badShapeExit` at such a target (`denoteLayer_ref_succ`), so without
it the proposition is false at a checked point of a malformed program. The load discharges it
from the checker's verdict (`layerRefsWF_of_typeOf`); it is a premise here, never a field of
`ProgramSource`. The worlds are the ones `J` ranges over (decisions row 175, `E4-TYPED-CE-022`):
the world's service table is the source's, as `MachineTyped.services` states it, since a
service read answers what the fiber's context holds, which membership reads at the world's
table (`ServicesFit`), at the type the checker reads off the source's (`Checker.check`'s
`service` arm); at another table the proposition is false. The point's completed view is typed
by `PointTyped` itself (row 175, `E4-TYPED-CE-021`). The three witnesses are
`Test/Program/TypedDenotation.lean`'s. -/
def DenotesTyped (root : ProgramSource) : Prop :=
  root.program.layerRefsWF = true →
    ∀ (w : World), w.serviceTy = root.sig.serviceTy → ∀ (p : Point) (e : NativeEff) (ty : EffTy),
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

/-- Row 148 (types TY-07): term soundness at `Fits`, by the native evaluation adapter. -/
theorem termFits (table : RowTable) : TermFits table :=
  fun _ _ _ _ _ _ hty henv hev => evalTerm_fits_native table henv hty hev

/-! ## M5 from the fundamental property

The loaded machine has one fiber, not running, whose code is the root's denotation; every other
clause of `J` is over an empty list or the empty context. So M5 is the root code's typing at
the initial world (`machineTyped_load`; decisions row 175: the code is read there only, and at
every world it is false for a program that reads a service), and that is `DenotesTyped` at the
root point
(`loadsTyped_of_denotesTyped`): `typeOfProgram` checks the program, under the source's signature
(`root.signature`, rows 111–114), after expanding its layer references
(`Program/Typing.lean:61-64`), `loadR` loads the program as written (`RuntimeR.lean:41-46`), and
the root point's typing reads the loaded node through the expansion's rounds (`PointTyped`,
decisions row 153 (b)), so the reduction holds for a program with references too. -/

/-- `MachineLive` holds on a running machine whose store owes nothing. -/
theorem machineLive_of_quiet (m : RState) (stuck : m.stuck = none)
    (due : m.state.deferreds.due = []) : MachineLive m := by
  refine ⟨stuck, fun o ho => ?_⟩
  rw [due] at ho
  cases ho

/-- **M5's builder.** A root whose loaded code is typed at the initial world over the source's
service table (row 112), and whose head is not a race marker, loads into `J` there. The code is
read at that world only (decisions row 175; before it this premise demanded every world, which is
false for a program that reads a service, `E4-TYPED-CE-022`). -/
theorem typedState_of_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none)
    (code : TypedProg root (initialWorld rootTy root.sig.serviceTy) rootTy
      (denoteR root.program root.program (rootPoint compileFuel))) :
    TypedState root rootTy (initialWorld rootTy root.sig.serviceTy)
      (loadR root.program fuel compileFuel) := by
  have declared : (initialWorld rootTy root.sig.serviceTy).Γ Api.root = some rootTy :=
    insert_here (fun _ : FiberId => (none : Option EffTy)) Api.root rootTy
  refine ⟨initial_world_valid_at _ _ root.program fuel compileFuel, ⟨?_, ?_, ?_⟩, ?_,
    schedulerState_load root.program fuel compileFuel,
    observerState_load root _ fuel compileFuel,
    registrationState_load root _ fuel compileFuel noMarker⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty hty
      change (initialWorld rootTy root.sig.serviceTy).Γ Api.root = some ty at hty
      rw [declared] at hty
      cases hty
      exact savedPosition_of_saved root _ rootTy _
        ⟨rootTy, code, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · exact servicesFit_empty _
  · intro race hr
    cases hr
  · exact ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h),
      ⟨(fun i v h => nomatch h)⟩, ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

/-- **M5's builder.** `typedState_of_load` with the loaded root's code clause, the quiet machine's
liveness and the source's well-formedness (decisions row 170, `MachineTyped.sourceWF`). -/
theorem machineTyped_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (sourceWF : root.program.layerRefsWF = true)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none)
    (code : TypedProg root (initialWorld rootTy root.sig.serviceTy) rootTy
      (denoteR root.program root.program (rootPoint compileFuel))) :
    MachineTyped root rootTy (initialWorld rootTy root.sig.serviceTy)
      (loadR root.program fuel compileFuel) := by
  have declared : (initialWorld rootTy root.sig.serviceTy).Γ Api.root = some rootTy :=
    insert_here (fun _ : FiberId => (none : Option EffTy)) Api.root rootTy
  refine ⟨typedState_of_load root rootTy fuel compileFuel noMarker code, rfl, ?_,
    machineLive_of_quiet _ rfl rfl, sourceWF⟩
  intro f hf _ _ _ _ ty hty
  change f ∈ [_] at hf
  rw [List.mem_singleton] at hf
  subst hf
  change (initialWorld rootTy root.sig.serviceTy).Γ Api.root = some ty at hty
  rw [declared] at hty
  cases hty
  exact ⟨rootTy, code, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

/-- **M5's reduction lemma, at the generated typed state** (seat A's
`ValueMembership.typedStateF_load`, moved here and restated over row 134's split): a root whose
loaded code is typed at every world, with no race marker at its head, loads into `TypedState` at
the initial world. It is `J`'s first component (`machineTyped_load`), so the argument is written
once; the battery keeps a one-line use. -/
theorem typedState_load_of_code (root : ProgramSource) (ty : EffTy) (fuel compileFuel : Nat)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none)
    (code : ∀ w, TypedProg root w ty (denoteR root.program root.program (rootPoint compileFuel))) :
    ∃ w, TypedState root ty w (loadR root.program fuel compileFuel) :=
  ⟨_, typedState_of_load root ty fuel compileFuel noMarker (code _)⟩

/-- **A checked program's layer references are well formed** (decisions row 170):
`typeOfProgram` answers only under `layerRefsWF` (`Program/Typing.lean:61-64`), so the load's
checker premise discharges `DenotesTyped`'s. -/
theorem layerRefsWF_of_typeOf {Op : Type} {sig : Signature Op} {program : Eff Op} {ty : EffTy}
    (h : Program.typeOfProgram sig program = some ty) : program.layerRefsWF = true := by
  unfold Program.typeOfProgram at h
  split at h
  · rename_i hc
    exact ((Bool.and_eq_true _ _).mp hc).1
  · cases h

/-- **M5 from row 148's fundamental property**, for a loaded head that is not a race marker
(`InterpR.lean:320`: only a race park builds one). The root point is typed by the checker's
verdict on the program's expansion (decisions row 153 (b)), so no reference-free premise: before
row 153 it carried `root.program.refSites [] = []` (`E4-TYPED-CE-019`,
`Test/Program/LayerRefs.lean`). The same verdict discharges the property's well-formedness
premise (row 170, `layerRefsWF_of_typeOf`); the initial world carries the source's service table
and the root point an empty completed view (row 175). -/
theorem loadsTyped_of_denotesTyped (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (denotes : DenotesTyped root)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none) :
    LoadsTyped root rootTy fuel compileFuel := by
  intro _ checked _
  have wf := layerRefsWF_of_typeOf checked
  have typed : effTy root.signature [] (Eff.expandIn root.program root.program) = some rootTy := by
    rw [Eff.expandIn_self]
    unfold Program.typeOfProgram at checked
    split at checked
    · exact checked
    · cases checked
  exact ⟨_, machineTyped_load root rootTy fuel compileFuel wf noMarker
    (denotes wf _ rfl (rootPoint compileFuel) root.program rootTy rfl
      ⟨root.program, [], rfl, Conform.Effect4.Typing.effTy_ok typed _, envTyped_nil _,
        fun _ h => nomatch h⟩)⟩

/-- **M5 from the layer family's arm** (`Typed/Denotation.lean`, `childDenotes_upto`: every arm of
`denoteR` by induction on fuel). The layer family's arm (`ProvideLayerArm`, decisions row 176 (b)) is
proved at every source in `Typed/LayerArm.lean` (`provideLayerArm`), where this closes
`M3bAssembly.denoteR_typed` (`denotesTyped`). -/
theorem denotesTyped_of_provideLayer (root : ProgramSource) (hlayer : ProvideLayerArm root) :
    DenotesTyped root := fun hwf w htie p e ty hat hpt =>
  childDenotes_upto root hlayer hwf p.fuel p.fuel (Nat.le_refl _) e p.path hat w htie p ty rfl rfl
    hpt

/-- **M5 on the layer-free fragment**: a program none of whose nodes is a `provideLayer` satisfies
the fundamental property; the layer family's arm cannot be reached there
(`provideLayerArm_of_layerFree`). -/
theorem denotesTyped_of_layerFree (root : ProgramSource) (h : LayerFree root.program) :
    DenotesTyped root :=
  denotesTyped_of_provideLayer root (provideLayerArm_of_layerFree h)

/-! ## World monotonicity of the bundle's saved positions (decisions rows 87 and 135)

Seat B's Kripke closure (row 135) proves the frame, stack, saved-frame and program laws in
`M3bWorld` (`Typed/Residual.lean`: `stackAccepts_mono`, `savedOk_mono`, `typedProg_mono`). The
bundle's `SavedOk` owner predicate is the stack and its provenance (row 134), so it transports
along the host order by `Contracts.stackAccepts_mono`, at a position the world already declares:
an undeclared position may become declared later, which is why that premise is there (seat B's
statement, first proved in `Test/Program/FramesNotKripke.lean`). It joins `M3bWorld` in the
ledger below (row 87: the monotonicity of every owner predicate of `preds` is declared there). -/

/-- **The bundle's `SavedOk` transports along the host order** at a position the world
declares. -/
theorem preds_savedOk_mono (root : ProgramSource) (w w' : World) (e : Expect) (x : RSaved)
    (ord : w.leHost w') (declared : (expectOf w e).isSome = true)
    (h : (preds root).SavedOk w e x) : (preds root).SavedOk w' e x := by
  intro ty hty
  obtain ⟨ty0, h0⟩ := Option.isSome_iff_exists.mp declared
  have same : expectOf w' e = some ty0 := by
    cases e with
    | root => exact ord.1.2.1 _ _ h0
    | fiber _ => exact ord.1.2.1 _ _ h0
    | hook _ => cases h0
  rw [same] at hty
  cases hty
  obtain ⟨tin, stack, provenance⟩ := h _ h0
  exact ⟨tin, positionStack_mono ord stack, provenance⟩

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
  rintro lawful checked row ⟨tape, free, rfl⟩
  obtain ⟨w₀, loaded⟩ := load lawful checked row
  letI := termEvaluatorFor root.program
  obtain ⟨w, _, typed⟩ := Machine.Lift.replayEval_lift hostOrder (MachineTyped root rootTy)
    (fun w m d => AnswerOk w m d) (interpR root.program) fuel
    (fun w m d _ held admitted => decisions d w m held admitted) tape w₀
    (loadR root.program fuel fuel) loaded
    (admittedReplay_noHostAnswer root (MachineTyped root rootTy) fuel tape free _)
  exact ⟨w, typed⟩

/-- The empty tape leaves the loaded machine. -/
theorem replayR_nil_machine (p : NativeEff) (fuel : Nat) :
    (replayR p fuel []).machine = loadR p fuel fuel := by
  unfold replayR replayEval
  split
  · rfl
  · split
    · rfl
    · rfl

/-- The loaded machine is reachable (the empty tape), so the capstone at the load is M5. -/
theorem rreachable_load (root : ProgramSource) (fuel : Nat) :
    RReachable root fuel (loadR root.program fuel fuel) :=
  ⟨[], (fun _ h => nomatch h), (replayR_nil_machine root.program fuel).symm⟩

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
    noRaceAfterInterrupt := fun _ _ _ h => (nomatch h), links := fun _ _ _ _ _ h => (nomatch h),
    raceObservers := fun _ _ _ h => (nomatch h) }

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

/-- The M7 fragment: a lawful source at the empty host table, checked and closed, its requirement
row empty (decisions row 117: rc.112's `runPromise` takes `Effect<A, E>`, `Effect.ts:17494-17497`),
and a tape with no host answer. -/
structure M7Fragment (root : ProgramSource) (rootTy : EffTy) (tape : List Api.Decision) :
    Prop where
  lawful : LawfulSource root
  emptyTable : root.table = []
  checked : Program.typeOfProgram root.signature root.program = some rootTy
  closedRow : rootTy.requires = Env.Requirement.empty
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
takes this as its validity premise. The scope arm of `HandleFits` reads the scope's presence
since decisions row 156 (the formal pass's `redA_scope` dangling handle no longer fits:
`Test/Program/ExitConnector.lean`, `dangling_scope_refused`), but `Live` still admits scope and
memo handles unchecked at `unknown`, so it does not yet follow from `J`; with those arms it is a
consequence of `J`, otherwise the native guard's handle facts transport through R4's bridge. -/
def ExitHandlesValid (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) : Prop :=
  LawfulSource root → Program.typeOfProgram root.signature root.program = some rootTy →
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
    obtain ⟨w, typed⟩ := capstone _ fragment.lawful fragment.checked
      fragment.closedRow ⟨tape, fragment.answerFree, rfl⟩
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

`typedState_load` (M5: initialization from an admitted source) and the denotation lemma, proved in
`Typed/LayerArm.lean`, where `M3bAssembly`'s report runs. The transition ledger (M6): one
preservation obligation per command constructor, one for a tape decision under admitted host
answers, and the capstone that every reachable state is typed. -/
namespace M3bAssembly

/-- Row 148: the fundamental property (algebra A3); proved in `Typed/LayerArm.lean` (`denotesTyped`). -/
theorem denoteR_typed (root : ProgramSource) : ProofGraph.Obligation (DenotesTyped root) := ⟨⟩

/-- Row 148: term soundness at `Fits` (types TY-07); seat A proves it. -/
theorem evalTerm_fits (table : RowTable) : ProofGraph.Obligation (TermFits table) := ⟨⟩

theorem typedState_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (LoadsTyped root rootTy fuel compileFuel) := ⟨⟩

/-- Row 176 (b): the layer family's arm (`ProvideLayerArm`, `Typed/Denotation.lean`), the one arm
`denotesTyped_of_provideLayer` takes as a hypothesis; proved in `Typed/LayerArm.lean`
(`provideLayerArm`). -/
theorem denoteR_typed_provideLayer (root : ProgramSource) :
    ProofGraph.Obligation (ProvideLayerArm root) := ⟨⟩

theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (_h : CaptureTyped root w c)
    (_hex : Fits w exVal (.exitOf .unknown .unknown))
    (_hview : ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2) :
    ProofGraph.Obligation
    (∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty) := ⟨⟩

end M3bAssembly

namespace M6Ledger

theorem step_evaluate (root : ProgramSource) (rootTy : EffTy) (id : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.evaluate id)) := ⟨⟩

/-- `E4-TYPED-CE-012` refuted it as declared at `dceae006` (one `loop` allocates a cell and no
world types the result: the saved stack does not transport along world growth,
`docs/research/2026-10-01-landing/ports-at-dceae006/HeadStepLoop.lean`). Repaired by seat B's
Kripke closure (row 135): the refutation is retained over the one-world judgment
(`Test/Program/FramesNotKripke.lean`, `step_loop_refuted`), and the same `loop` with a frame typed
into `unit` keeps `I` at the world that declares the new cell (`step_loop_good`, over this split).
Its halting arms (the census in `MachineLive`'s section) read the target and scope premises
`fiberPre` carries on the halting rows (row 139); the absent-scope callback that refuted
`step_deliver` before row 156 reaches the same walk from `loop` (`Laws/Program/EvaluateR.lean`
`:309-319`; reading, not checked here); since rows 156 and 188 (a) the callback is typed only at a
`scoped` guard's run position, where the scope is present. `E4-TYPED-CE-033` (a registration
marker under an injected yield) refuted this statement at `53caad0f`; decisions row 188 (b). -/
theorem step_loop (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.loop id yielding)) := ⟨⟩

/-- Open. `E4-SCHED-CE-020`'s witness under `J`'s `stuck = none` refuted it before decisions row
156: a configuration typed by a judgment whose `scopeExit` constructor read no pre delivered into
a scope-exit marker for the absent scope 0 and halted (`prepareScopedExitR`); that refutation is
kept as history over a local copy of that judgment
(`M6Capstone.H1HaltAmendment.step_deliver_refuted_by_absent_scope`). Since row 156 the
constructor carries the scope's presence (`ScopeLive`), and the witness's input is no typed
configuration at any world (`M6Capstone.H1HaltAmendment.input_refused`), so it no longer refutes
this obligation. `E4-TYPED-CE-034` refuted it again at `53caad0f` with the scope present: the
general constructor typed a raw marker as current code, which the counted step answers
`badShapeExit`. Decisions row 188 (a) types the callback only at the `scoped` guard's run position
(`TypedProg.scopedGuard`, `FrameAccepts.scopedResume`, the walk's `CallbackSaved`); the witness's
input is refused at every world (`Test/Program/ScopeExitCallback.lean`, `input_refused`). -/
theorem step_deliver (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.deliver id yielding)) := ⟨⟩

theorem step_finish (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (exit : ExitV) :
    ProofGraph.Obligation (StepPreserves root rootTy (.finish id exit)) := ⟨⟩

theorem step_resume (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (token : Nat) (code : RProgram) :
    ProofGraph.Obligation (StepPreserves root rootTy (.resume id token code)) := ⟨⟩

/-- Proved in `Typed/Commands/Launch.lean` (`launch_preserves`): the entrant is allocated at the
old `nextId` and declared at the race's result type. Its transport needs every negative read of the
fiber table at an id below `nextId` (decisions rows 134 (e) and 189). -/
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

`E4-TYPED-CE-009` (`Fits` compared declared types in the raw order while the checker
normalizes, so M5 was false for a checked program) is repaired by row 137 (seat A):
`Test/Counterexamples/Machine/Semantics/FitsOrder.lean` proves M5's proposition and this
capstone's at that program's loaded machine, which the empty tape reaches (`rreachable_load`;
`loadsTyped`, `capstone_at_load`), and keeps the refutations over the raw leaf
(`Reviewed.m5_false`, `Reviewed.loadsTyped_false`, `Reviewed.capstone_false`; seat C's
restatement over `J`, `RawOrderLoad.lean`, is history under the same hypothesis).
`E4-TYPED-CE-018` (the posts that answer a scope handle carry no presence, so an allocation's
continuation must be typed at an absent scope; registered from Codex's second-eyes review,
`docs/research/2026-10-01-landing/codex-second-eyes/ScopeAllocationPost.lean`) refutes
`DenotesTyped` at a checked allocate-then-fork program and is open under decisions row 156.
`E4-TYPED-CE-010` (the await-by-value post read the
target's answer column, so M5 was false for the typed corpus's `awaitFiber.value`) is repaired by
row 136's post: `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean` proves M5's proposition
and this capstone's at that program's loaded machine (`loadsTyped`, `capstone_at_load`) and keeps
the refutation over the old post (`loadsTyped_false`, `capstone_false`, over `OldMachineTyped`).
`E4-TYPED-CE-011` (the saved-code clause read at a budget cut) refuted the
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

/-! Row 87: the bundle's owner predicates' world monotonicity joins seat B's `M3bWorld`
(`Typed/Residual.lean`), whose report runs at the foot of this module, after this goal. -/
namespace M3bWorld

/-- Row 87's transport for the bundle's `SavedOk` at a position the world declares (seat B's
ledger line, receipt-B "For seat C" item 2). -/
theorem preds_savedOk_mono (root : ProgramSource) (w w' : World) (e : Expect) (x : RSaved) :
    ProofGraph.Obligation (w.leHost w' → (expectOf w e).isSome = true →
      (preds root).SavedOk w e x → (preds root).SavedOk w' e x) := ⟨⟩

end M3bWorld

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M3bAssembly.capture_lookup :=
  @Effect4.Program.Typed.capture_lookup
#obligation_proved Effect4.Program.Typed.M3bAssembly.evalTerm_fits :=
  @Effect4.Program.Typed.termFits
-- `M3bAssembly`'s report runs at the foot of `Typed/LayerArm.lean`, which proves its last three goals
-- (the import direction forbids this module naming the proofs; decisions row 140)
#proof_wanted Effect4.Program.Typed.M6Ledger.step_loop
#proof_wanted Effect4.Program.Typed.M6Ledger.step_deliver
#proof_wanted Effect4.Program.Typed.M6Ledger.decision_preserves
#proof_wanted Effect4.Program.Typed.M6Ledger.typedState_reachable
-- `M6Ledger`'s proved goals and its report are at the foot of the last command module
-- (`Typed/Commands/*.lean`), which imports this one and sees every proof.
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
-- `M6Edits`' report is at `Typed/Edits.lean`'s foot, which imports this module and proves six goals.
#obligation_proved Effect4.Program.Typed.M3bWorld.preds_savedOk_mono :=
  @Effect4.Program.Typed.preds_savedOk_mono
#obligation_audit Effect4.Program.Typed.M3bWorld
#typed_state_obligations Effect4.Program.Typed.M3bWorld ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])
