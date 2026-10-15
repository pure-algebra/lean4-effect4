import Effect4.Laws.Machine.ContextualMessages
import Effect4.Laws.Machine.LiftMachineFact
import Effect4.Laws.Machine.AnswerFlowFamily
import Effect4.Laws.Machine.Ledger

/-!
# The answer flow of every fiber, through decisions

Concepts: store-typing R4 and scope-lifetime-finalization R11, the saved answer classes; and
reactive-scheduling, the invariant over execution traces.
Question: the whole-history producer of answer flow, the proposed registry claim
`answer-flow-history` (role preservation). Its consumers are the crews' answer-class instance, then
`Workers.Assertions.logs_step`, `QueueWorkers.Assertions.logs_history` and both Timeout goals
through their writer ledgers (seat GOALS-2's receipt, §4.3).
Reach: every interpreter, world order, decision invariant and admission. The flow is a predicate of
each stored fiber's frame, read at the world that fiber reads (`Flows`).
Limit: the command step and the reply are premises; the producer states no answer class of a
program, no progress and no host observation.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Machine

universe u v w w'

section Flows

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable {World : Type w}

/-- **The flow of every stored fiber**: each fiber's frame holds `G` at the world it reads. The
world reads the store and the fiber's id, so a write that keeps both, and the frame, keeps it. -/
def Flows (G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop) (worldOf : St → FiberId → World)
    (m : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame

variable {G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop} {worldOf : St → FiberId → World}

/-- A write that keeps the stored fibers and the store keeps the flow. A step of every edit below. -/
theorem Flows.fields {m n : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m)
    (fibers : n.fibers = m.fibers) (state : n.state = m.state) : Flows G worldOf n := by
  intro f member
  rw [state]
  exact held f (fibers ▸ member)

/-- Installing a fiber that holds its flow keeps every other fiber's. A step of the decision
edits, and of every command that writes one fiber back. -/
theorem Flows.update {m : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m)
    (f : RunFiber ν σ β ε δ ι α χ) (new : G (worldOf m.state f.id) f.id f.frame) :
    Flows G worldOf (m.update f) := by
  intro g member
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  rw [← same]
  change G (worldOf m.state (if old.id = f.id then f else old).id)
    (if old.id = f.id then f else old).id (if old.id = f.id then f else old).frame
  split
  · exact new
  · exact held old present

/-- An edit of one fiber that keeps its id and frame keeps the flow. A step of the yield verdict
and of every metadata write. -/
theorem Flows.modify {m : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m) (id : FiberId)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (key : ∀ f, (edit f).id = f.id) (frame : ∀ f, (edit f).frame = f.frame) :
    Flows G worldOf (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i f found
    apply held.update
    rw [key, frame]
    exact held f (RunMachine.mem_of_fiber? found)

/-- A store that every stored fiber's flow survives keeps the flow. A step of the clock, of reply
preparation and of every store hook. -/
theorem Flows.state {m : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m) (next : St)
    (stable : ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame →
      G (worldOf next f.id) f.id f.frame) :
    Flows G worldOf {m with state := next} :=
  fun f member => stable f member (held f member)

end Flows

/-! ## The edits a decision makes outside the command loop -/

section Edits

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {World : Type w}

/-- **The store facts of the outside edits.** The clock and reply preparation keep every stored
fiber's flow. The interrupt decision records at its target, which the commands' interrupt fact
covers. The dispatcher drain, the `ranTask` event, a yield verdict, the middleware latch and an owed
resume write no frame and no store, so they owe nothing. -/
structure OutsideEdits (interp : RunInterp ν σ β ε δ ι α χ St)
    (G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop) (worldOf : St → FiberId → World) :
    Prop where
  clock : ∀ (m : RunMachine ν σ β ε δ ι α χ St) millis, m.stuck = none →
    ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame →
      G (worldOf (interp.clockStep millis m.state).2 f.id) f.id f.frame
  prepare : ∀ (m : RunMachine ν σ β ε δ ι α χ St) id token answer,
    ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame →
      G (worldOf (prepareAsyncAnswer interp m id token answer).1 f.id) f.id f.frame

variable {interp : RunInterp ν σ β ε δ ι α χ St}
variable {G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop} {worldOf : St → FiberId → World}

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- An owed resume posts a task or returns a command: it writes no frame and no store. A step of
`OutsideEdits.machineEdits`. -/
theorem Flows.drainOwed (m : RunMachine ν σ β ε δ ι α χ St) (held : Flows G worldOf m) :
    ∀ owed : List (Owed (Prim ν σ β ε δ ι α)), Flows G worldOf (Machine.drainOwed m owed).1
  | [] => held
  | first :: rest => by
    simp only [Machine.drainOwed]
    cases first.mode with
    | now => exact Flows.drainOwed m held rest
    | scheduled owner priority =>
      apply Flows.drainOwed
      unfold RunMachine.postTask
      split
      · exact held.fields rfl rfl
      · rename_i fiber found
        have kept : G (worldOf m.state fiber.id) fiber.id fiber.frame :=
          held fiber (RunMachine.mem_of_fiber? found)
        let task : Machine.Task ν σ β ε δ ι α := .resume first.waiter first.token first.code
        exact (held.update {fiber with dispatcher := fiber.dispatcher.enqueue priority task} kept).fields rfl rfl

/-- **The outside edits keep the flow.** The interrupt decision records at its target; the clock
and the prepared reply move the store; the other five edits write no frame and no store. -/
theorem OutsideEdits.machineEdits (edits : OutsideEdits interp G worldOf)
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame) :
    Lift.MachineEdits interp (Flows G worldOf) where
  drain := by
    intro m owner fiber held found
    have updated := held.update {fiber with dispatcher := fiber.dispatcher.drain.2}
      (held fiber (RunMachine.mem_of_fiber? found))
    exact updated.fields rfl rfl
  ran := fun m _ _ held => held.fields rfl rfl
  yield := fun m id _ held => held.modify id _ (fun _ => rfl) (fun _ => rfl)
  interrupt := by
    intro m who extra target fiber held found
    have recorded := interruption m.state (interruptCause interp who extra fiber.id) fiber
      (held fiber (RunMachine.mem_of_fiber? found))
    have key := StackLedger.interruptRecord_key interp who extra fiber
    unfold Lift.interruptEdit
    dsimp only
    split
    · apply Flows.update (held.fields rfl rfl)
      rw [key]
      exact recorded
    · apply Flows.update (held.fields rfl rfl)
      rw [key]
      exact recorded
  middleware := fun m held => held.fields rfl rfl
  clock := fun m millis held running => held.state _ (edits.clock m millis running)
  owed := fun m owed held => Flows.drainOwed m held [owed]
  prepare := fun m id token answer held => held.state _ (edits.prepare m id token answer)

end Edits

/-! ## The commands

Each command writes at most one frame of its own, through one of a few writes: an evaluation's
installed fiber, a reply installed as the current code, an entrant or a child's start, a cleanup or
a parked registration, an interrupt record, a published or cleared exit. The local facts name each
such write once (`Commands`); every other write keeps the frame and the store, and so the flow. -/

section Commands

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {World : Type w}
variable {G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop} {worldOf : St → FiberId → World}

/-- An iteration's result keeps the flow once its fiber is installed: every fiber of the installed
machine, and the returned fiber itself, at the store the iteration left. -/
def IterFlows (G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop)
    (worldOf : St → FiberId → World) (it : Iter ν σ β ε δ ι α χ St) : Prop :=
  Flows G worldOf (it.machine.update it.fiber) ∧
    G (worldOf it.machine.state it.fiber.id) it.fiber.id it.fiber.frame

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Replacing an installed fiber by one with its id and frame keeps the flow. A step of the
settlement writes. -/
theorem Flows.update_same {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    (held : Flows G worldOf (m.update f)) (good : G (worldOf m.state f.id) f.id f.frame)
    (next : RunFiber ν σ β ε δ ι α χ) (key : next.id = f.id) (frame : next.frame = f.frame) :
    Flows G worldOf (m.update next) := by
  intro g member
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  rw [← same]
  change G (worldOf m.state (if old.id = next.id then next else old).id)
    (if old.id = next.id then next else old).id (if old.id = next.id then next else old).frame
  split
  · rw [key, frame]
    exact good
  · rename_i other
    have kept : old ∈ (m.update f).fibers := by
      apply List.mem_map.mpr
      refine ⟨old, present, ?_⟩
      rw [if_neg (by rw [← key]; exact other)]
    exact held old kept

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A stored fiber's flow, read off the machine. -/
theorem Flows.found {m : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m) {id : FiberId}
    {f : RunFiber ν σ β ε δ ι α χ} (found : m.fiber? id = some f) :
    G (worldOf m.state f.id) f.id f.frame :=
  held f (RunMachine.mem_of_fiber? found)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Installing a record with a found fiber's id and frame keeps the flow. A step of every metadata
write at a looked-up fiber. -/
theorem Flows.update_found {m : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m) {id : FiberId}
    {f : RunFiber ν σ β ε δ ι α χ} (found : m.fiber? id = some f) (next : RunFiber ν σ β ε δ ι α χ)
    (key : next.id = f.id) (frame : next.frame = f.frame) : Flows G worldOf (m.update next) := by
  apply held.update next
  rw [key, frame]
  exact held.found found

/-- **The local facts of the commands.** `Ready` is what the base invariant gives at a command. -/
structure Commands [FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α)
      (FrameEvent ν σ β ε δ ι α)]
    (interp : RunInterp ν σ β ε δ ι α χ St)
    (Ready : RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop)
    (G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop) (worldOf : St → FiberId → World) : Prop where
  /-- One iteration of the acting fiber: its own evaluation, the stores it writes, the fibers it
  starts. -/
  iteration : ∀ m (f : RunFiber ν σ β ε δ ι α χ) yielding, Ready m (.loop f.id yielding) →
    Flows G worldOf m → m.fiber? f.id = some f → IterFlows G worldOf (iteration interp m f yielding)
  /-- One delivery: the evaluation without the loop top. -/
  deliver : ∀ m (f : RunFiber ν σ β ε δ ι α χ) yielding, Ready m (.deliver f.id yielding) →
    Flows G worldOf m → m.fiber? f.id = some f →
      IterFlows G worldOf (FiberEvaluator.evaluate interp m f yielding)
  /-- An interrupt delta keeps the fiber's flow: it records the cause, and it may set the deferred
  flag or fail the fiber with the accumulated cause. -/
  interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
    G (worldOf state f.id) f.id f.frame →
      G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame
  /-- A reply that a parked fiber's token admits becomes its current code. -/
  resume : ∀ m id token code (t : RunFiber ν σ β ε δ ι α χ), Ready m (.resume id token code) →
    Flows G worldOf m → m.fiber? id = some t → t.parked = .withGuard token →
      G (worldOf m.state t.id) t.id {t.frame with current := code}
  /-- A race entrant starts at the next id with its program, interruptible. -/
  entrant : ∀ m raceId (race : Race ν σ β ε δ ι α (Prim ν σ β ε δ ι α)) program more
    (host : RunFiber ν σ β ε δ ι α χ), Ready m (.launch raceId) → Flows G worldOf m →
    m.race? raceId = some race → race.programs = program :: more →
    m.fiber? race.host = some host →
      G (worldOf m.state ⟨m.nextId⟩) ⟨m.nextId⟩
        (RunFiber.make ⟨m.nextId⟩ program true (interp.budgetOf host.context) host.context :
          RunFiber ν σ β ε δ ι α χ).frame
  /-- A buffered race answer becomes the host's current code. -/
  settleRace : ∀ m raceId yielding (race : Race ν σ β ε δ ι α (Prim ν σ β ε δ ι α))
    (f : RunFiber ν σ β ε δ ι α χ) exit, Ready m (.registrationDone raceId yielding) →
    Flows G worldOf m → m.race? raceId = some race → m.fiber? race.host = some f →
    race.state.accepted = some exit →
      G (worldOf m.state f.id) f.id {f.frame with current := interp.raceSettle raceId race.state.cleanupNeeded exit}
  /-- A race registration with no answer pushes its cancel frame and parks. -/
  parkRace : ∀ m raceId yielding (race : Race ν σ β ε δ ι α (Prim ν σ β ε δ ι α))
    (f : RunFiber ν σ β ε δ ι α χ), Ready m (.registrationDone raceId yielding) →
    Flows G worldOf m → m.race? raceId = some race → m.fiber? race.host = some f →
      G (worldOf m.state f.id) f.id {f.frame with stack := .asyncFinalizer (interp.cancelName (interp.raceCancelName raceId) f.id race.token) :: f.frame.stack}
  /-- The await an interrupt returns becomes the host's current code. -/
  afterInterrupt : ∀ m host yielding kind (f : RunFiber ν σ β ε δ ι α χ),
    Ready m (.afterInterrupt host yielding kind) → Flows G worldOf m → m.fiber? host = some f →
      G (worldOf m.state f.id) f.id {f.frame with current := asVoidCode interp (awaitCode interp m kind)}
  /-- A parallel close awaits its forked finalizers under the generator frame. -/
  closePar : ∀ m host yielding fibers (f : RunFiber ν σ β ε δ ι α χ),
    Ready m (.closeParAwait host yielding fibers) → Flows G worldOf m → m.fiber? host = some f →
      G (worldOf m.state f.id) f.id {f.frame with current := interp.parkCode (.awaitAll fibers), stack := .iterator interp.closeDoneName interp.voidValue :: f.frame.stack}
  /-- The children's interrupt becomes the current code of an exiting fiber. -/
  exitChildren : ∀ m id exit (f : RunFiber ν σ β ε δ ι α χ), Ready m (.finish id exit) →
    Flows G worldOf m → m.fiber? id = some f →
    (m.middlewareInstalled && f.finalizing.isNone && !f.children.isEmpty) = true →
      G (worldOf m.state f.id) f.id {f.frame with deferredInterrupt := false, current := .onSuccess (interp.interruptAllCode f.children) (interp.restoreName exit)}
  /-- Publishing an exit clears the deferred flag. -/
  publish : ∀ (state : St) (f : RunFiber ν σ β ε δ ι α χ),
    G (worldOf state f.id) f.id f.frame →
      G (worldOf state f.id) f.id {f.frame with deferredInterrupt := false}
  /-- Clearing an exited fiber empties its saved stack. -/
  cleared : ∀ (state : St) (f : RunFiber ν σ β ε δ ι α χ),
    G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id {f.frame with stack := []}
  /-- The store hooks keep every stored fiber's flow. -/
  link : ∀ (m : RunMachine ν σ β ε δ ι α χ St) mode scope target state key,
    interp.scopeLinkFiber mode scope target m.state = some (state, key) →
    ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame → G (worldOf state f.id) f.id f.frame
  drop : ∀ (m : RunMachine ν σ β ε δ ι α χ St) scope key state,
    interp.dropFinalizer scope key m.state = some state →
    ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame → G (worldOf state f.id) f.id f.frame
  due : ∀ (m : RunMachine ν σ β ε δ ι α χ St), ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame →
    G (worldOf (interp.dueResumes m.state).2 f.id) f.id f.frame
  wake : ∀ (m : RunMachine ν σ β ε δ ι α χ St) list phase, ∀ f ∈ m.fibers,
    G (worldOf m.state f.id) f.id f.frame →
      G (worldOf (interp.wakeList list phase m.state) f.id) f.id f.frame

variable {Ready : RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop}

/-- An addressed edit keeps the flow: an observer and a dropped token write no frame, and an
interrupt delta keeps its target's. A step of settlement and of the scope link. -/
theorem Flows.fiberEdit
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame)
    (edit : FiberEdit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St) (held : Flows G worldOf m) :
    Flows G worldOf (applyFiberEdit edit m).1 := by
  cases edit with
  | observe target observer => exact held.modify target _ (fun _ => rfl) (fun _ => rfl)
  | dropToken token =>
    intro f member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    exact held old present
  | interrupt target cause =>
    simp only [applyFiberEdit]
    split
    · exact held
    · rename_i f found
      apply held.update
      rw [StackLedger.interruptWithCause_key]
      exact interruption m.state cause f (held.found found)

/-- An addressed edit word keeps the flow. A step of settlement and of the scope link. -/
theorem Flows.fiberEdits
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame)
    (edits : List (FiberEdit ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) (held : Flows G worldOf m) :
    Flows G worldOf (applyFiberEdits edits m).1 := by
  have facts : ContextualMessages.Local Lift.unitOrder
      (fun (_ : Unit) (_ : Unit) m => Flows G worldOf m)
      (fun (_ : Unit) (_ : Unit) (_ : RunMachine ν σ β ε δ ι α χ St)
        (_ : List (Cmd ν σ β ε δ ι α)) => True) := by
    refine { observe := ?_, drop := ?_, interrupt := ?_ }
    · intro context world m commands target observer flow queued
      refine ⟨(), Lift.unitOrder.refl (), ?_, True.intro⟩
      exact Flows.fiberEdit interruption (.observe target observer) m flow
    · intro context world m commands token flow queued
      refine ⟨(), Lift.unitOrder.refl (), ?_, True.intro⟩
      exact Flows.fiberEdit interruption (.dropToken token) m flow
    · intro context world m commands target cause fiber found flow queued
      refine ⟨(), Lift.unitOrder.refl (), ?_, True.intro⟩
      have changed := Flows.fiberEdit interruption (.interrupt target cause) m flow
      simpa only [applyFiberEdit, found] using changed
  obtain ⟨world, advanced, retained, queued⟩ := facts.apply () () edits m held True.intro
  exact retained

/-- Settlement keeps the flow of an iteration's result: it installs the returned fiber, applies the
edit word and records the outcome in metadata. -/
theorem Flows.settle
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) (it : Iter ν σ β ε δ ι α χ St)
    (ready : IterFlows G worldOf it) : Flows G worldOf (Machine.settle id rest it).1 := by
  have outcome (it : Iter ν σ β ε δ ι α χ St) (ready : IterFlows G worldOf it) :
      Flows G worldOf (settleOutcome id rest it).1 := by
    unfold settleOutcome
    split
    · exact ready.1
    · exact ready.1
    · split
      · exact ready.1.update_same ready.2 {it.fiber with parked := .notParked, pending := []} rfl rfl
      · exact ready.1.update_same ready.2 {it.fiber with running := false} rfl rfl
    · exact ready.1
    · exact ready.1
    · exact (ready.1.update_same ready.2 {it.fiber with running := false} rfl rfl).fields rfl rfl
  unfold Machine.settle
  split
  · exact outcome it ready
  · dsimp only
    have changed := Flows.fiberEdits interruption it.edits _ ready.1
    split
    · exact changed.fields rfl rfl
    · rename_i owner found
      apply outcome
      exact ⟨changed.update owner (changed.found found), changed.found found⟩

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A fiber appended at a fresh id with its flow keeps the flow. A step of a race entrant's start. -/
theorem Flows.append {m n : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m)
    (child : RunFiber ν σ β ε δ ι α χ) (new : G (worldOf m.state child.id) child.id child.frame)
    (fibers : n.fibers = m.fibers ++ [child]) (state : n.state = m.state) : Flows G worldOf n := by
  intro f member
  rw [state]
  rw [fibers] at member
  rcases List.mem_append.mp member with old | fresh
  · exact held f old
  · rw [List.mem_singleton.mp fresh]
    exact new

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A race entrant's start keeps the flow when the entrant holds its own. -/
theorem Flows.launchEntrant (interp : RunInterp ν σ β ε δ ι α χ St) (raceId : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (site : List Nat) (held : Flows G worldOf m)
    (new : G (worldOf m.state ⟨m.nextId⟩) ⟨m.nextId⟩
      (RunFiber.make ⟨m.nextId⟩ program true (interp.budgetOf host.context) host.context :
        RunFiber ν σ β ε δ ι α χ).frame) :
    Flows G worldOf (Machine.launchEntrant interp raceId m host program site).1 :=
  Flows.append held (RunFiber.make ⟨m.nextId⟩ program true (interp.budgetOf host.context) host.context)
    new rfl rfl

/-- Interrupting a target list keeps the flow: each target takes an interrupt delta. A step of the
countdown observer's fail-fast arm. -/
theorem Flows.interruptEach (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame)
    (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId) :
    ∀ (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)), Flows G worldOf acc.1 →
      Flows G worldOf (Machine.interruptEach interp who extra targets acc).1 := by
  induction targets with
  | nil => intro acc held; exact held
  | cons target rest ih =>
    intro acc held
    unfold Machine.interruptEach
    rw [List.foldl_cons]
    split
    · exact ih acc held
    · rename_i g found
      apply ih
      have recorded : G (worldOf acc.1.state (interruptRecord interp (some who) extra g).1.id)
          (interruptRecord interp (some who) extra g).1.id (interruptRecord interp (some who) extra g).1.frame := by
        rw [StackLedger.interruptRecord_key]
        exact interruption acc.1.state _ g (held.found found)
      generalize interruptRecord interp (some who) extra g = r at recorded ⊢
      obtain ⟨next, applyNow⟩ := r
      exact (held.update next recorded).fields rfl rfl

/-- One observer keeps the flow. A dropped scope finalizer writes the store; the countdown's
fail-fast arm interrupts; every other arm writes metadata, races or the trace. -/
theorem Flows.fireObserver (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame)
    (drop : ∀ (m : RunMachine ν σ β ε δ ι α χ St) scope key state,
      interp.dropFinalizer scope key m.state = some state →
      ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame → G (worldOf state f.id) f.id f.frame)
    (id : FiberId) (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (observer : Observer) (held : Flows G worldOf acc.1) :
    Flows G worldOf (Machine.fireObserver interp id exit acc observer).1 := by
  have base : Flows G worldOf (acc.1.emit [RunEvent.observerFired id observer]) := held.fields rfl rfl
  unfold Machine.fireObserver
  dsimp only
  split
  · exact base
  · exact base.modify _ _ (fun _ => rfl) (fun _ => rfl)
  · split
    · exact base.fields rfl rfl
    · rename_i state found
      exact base.state state (drop _ _ _ state found)
  · rename_i waiter token
    split
    · exact base
    · split
      · exact base
      · rename_i p _
        split
        · have changed : Flows G worldOf (if p.failFast && !exit.isSuccess && p.collected.all Exit.isSuccess then
              Machine.interruptEach interp waiter (interp.stackAnnotations waiter) p.remaining
                (acc.1.emit [RunEvent.observerFired id (.countdown waiter token)], [])
              else (acc.1.emit [RunEvent.observerFired id (.countdown waiter token)], [])).1 := by
            split
            · exact Flows.interruptEach interp interruption waiter _ p.remaining _ base
            · exact base
          split
          · exact changed
          · rename_i current currentFound
            split
            · exact changed
            · split
              · exact changed.update_found currentFound _ rfl rfl
              · exact Flows.fiberEdit interruption _ _ (changed.update_found currentFound _ rfl rfl)
        · exact base
  · split
    · exact base
    · split
      · exact ((base.fields rfl rfl).fields rfl rfl).fields rfl rfl
      · exact base.fields rfl rfl
  · exact base.fields rfl rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The exit path keeps the flow: the children's interrupt installed, or the exit published and,
with no observer, the fiber cleared. -/
theorem Flows.exitFiber (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) (held : Flows G worldOf m)
    (children : (m.middlewareInstalled && f.finalizing.isNone && !f.children.isEmpty) = true →
      G (worldOf m.state f.id) f.id {f.frame with deferredInterrupt := false, current := .onSuccess (interp.interruptAllCode f.children) (interp.restoreName exit)})
    (publish : G (worldOf m.state f.id) f.id {f.frame with deferredInterrupt := false})
    (cleared : G (worldOf m.state f.id) f.id {f.frame with deferredInterrupt := false, stack := []}) :
    Flows G worldOf (Machine.exitFiber interp m f exit).1 := by
  unfold Machine.exitFiber
  split
  · rename_i runs
    unfold Machine.exitFiber.exitInterruptChildren
    exact (held.update _ (children runs)).fields rfl rfl
  · unfold Machine.exitFiber.exitStore
    dsimp only
    have published : Flows G worldOf ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit]) :=
      (held.update _ publish).fields rfl rfl
    split
    · exact published.update _ cleared
    · exact published

/-- The scope link keeps the flow: its store write, then its edit word. -/
theorem Flows.linkScope (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame)
    (link : ∀ (m : RunMachine ν σ β ε δ ι α χ St) mode scope target state key,
      interp.scopeLinkFiber mode scope target m.state = some (state, key) →
      ∀ f ∈ m.fibers, G (worldOf m.state f.id) f.id f.frame → G (worldOf state f.id) f.id f.frame)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α) (held : Flows G worldOf m) :
    Flows G worldOf (Machine.linkScope interp m mode scope target who extra).1 := by
  unfold Machine.linkScope
  apply Flows.fiberEdits interruption
  unfold linkScopeEdits
  split
  · exact held.fields rfl rfl
  · split
    · exact held.fields rfl rfl
    · exact held.fields rfl rfl
  · split
    · exact held.fields rfl rfl
    · split
      · exact held
      · split
        · exact held.fields rfl rfl
        · rename_i state key found
          exact (held.state state (link m mode scope target state key found)).fields rfl rfl

variable [FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α)
  (FrameEvent ν σ β ε δ ι α)]
variable {interp : RunInterp ν σ β ε δ ι α χ St}

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  [FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α)] in
/-- Installing a fiber with its flow, then emitting, keeps the flow. A step of `Commands.step`. -/
theorem Flows.update_emit {m : RunMachine ν σ β ε δ ι α χ St} (held : Flows G worldOf m)
    (f : RunFiber ν σ β ε δ ι α χ) (new : G (worldOf m.state f.id) f.id f.frame)
    (events : List (RunEvent ν σ β ε δ ι α χ)) : Flows G worldOf ((m.update f).emit events) :=
  (held.update f new).fields rfl rfl

omit [FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α)
  (FrameEvent ν σ β ε δ ι α)] in
/-- Settling a one-fiber iteration over a flowing machine keeps the flow. A step of
`Commands.step`. -/
theorem Flows.settle_one
    (interruption : ∀ (state : St) cause (f : RunFiber ν σ β ε δ ι α χ),
      G (worldOf state f.id) f.id f.frame → G (worldOf state f.id) f.id (interruptWithCause cause f).1.frame)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) {m : RunMachine ν σ β ε δ ι α χ St}
    (held : Flows G worldOf m) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (outcome : Outcome ν σ β ε δ ι α) (good : G (worldOf m.state f.id) f.id f.frame) :
    Flows G worldOf (Machine.settle id rest ⟨m, f, yielding, outcome, [], []⟩).1 :=
  Flows.settle interruption id rest _ ⟨held.update f good, good⟩

/-- **Every command keeps the flow**, from the local facts of the commands. Placement: a step of
the producer (`Local.decision_lift`); reach: every interpreter, evaluator, machine and command. -/
theorem Commands.step (facts : Commands interp Ready G worldOf) (m : RunMachine ν σ β ε δ ι α χ St)
    (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α)) (ready : Ready m c)
    (held : Flows G worldOf m) : Flows G worldOf (driveStep interp m c rest).1 := by
  cases c with
  | evaluate id =>
    simp only [driveStep]
    split
    · exact held
    · rename_i f found
      split
      · exact held
      · exact held.update_emit {f with running := true, currentOpCount := 0}
          (held f (RunMachine.mem_of_fiber? found)) _
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i f found
      have key := RunMachine.id_of_fiber? found
      subst key
      exact Flows.settle facts.interruption _ rest _ (facts.iteration m f yielding ready held found)
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i f found
      have key := RunMachine.id_of_fiber? found
      subst key
      exact Flows.settle facts.interruption _ rest _ (facts.deliver m f yielding ready held found)
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact held
    · rename_i t found
      split
      · rename_i parkedToken parked
        split
        · rename_i same
          subst same
          exact held.update_emit _ (facts.resume m id parkedToken answer t ready held found parked) _
        · exact held
      · exact held
  | launch raceId =>
    simp only [driveStep]
    split
    · exact held
    · rename_i race raceFound
      split
      · exact held
      · rename_i program more programs
        split
        · exact held
        · split
          · exact held
          · rename_i host hostFound
            have launched := Flows.launchEntrant interp raceId m host program (race.nextSite.getD []) held
              (facts.entrant m raceId race program more host ready held raceFound programs hostFound)
            generalize launchEntrant interp raceId m host program (race.nextSite.getD []) = pair at launched ⊢
            obtain ⟨spawned, child⟩ := pair
            exact launched.fields rfl rfl
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · rename_i race c raceFound childFound
      split
      · rename_i exit exited
        have kept := Flows.fireObserver interp facts.interruption facts.drop child exit
          (m.updateRace {race with state := {race.state with live := race.state.live ++ [child]}}, [])
          (.raceCallback raceId) (held.fields rfl rfl)
        generalize Machine.fireObserver interp child exit
          (m.updateRace {race with state := {race.state with live := race.state.live ++ [child]}}, [])
          (.raceCallback raceId) = pair at kept ⊢
        obtain ⟨changed, nested⟩ := pair
        exact kept
      · have base : Flows G worldOf
            (m.updateRace {race with state := {race.state with live := race.state.live ++ [child]}}) :=
          held.fields rfl rfl
        refine base.modify child _ ?_ ?_
        · exact fun _ => rfl
        · exact fun _ => rfl
    · exact held
  | registrationDone raceId yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i race raceFound
      split
      · exact held.fields rfl rfl
      · rename_i f found
        have base : Flows G worldOf (m.updateRace {race with registering := false}) := held.fields rfl rfl
        split
        · rename_i exit accepted
          exact Flows.settle_one facts.interruption _ rest base
            {f with frame := {f.frame with current := interp.raceSettle raceId race.state.cleanupNeeded exit}}
            yielding _ (facts.settleRace m raceId yielding race f exit ready held raceFound found accepted)
        · have parked : Flows G worldOf ((m.updateRace {race with registering := false}).emit
              [RunEvent.parkedOn f.id race.token]) := base.fields rfl rfl
          exact Flows.settle_one facts.interruption _ rest parked
            (RunFiber.park {f with frame := {f.frame with stack := .asyncFinalizer (interp.cancelName (interp.raceCancelName raceId) f.id race.token) :: f.frame.stack}} ⟨race.token, none, [], [], .void, false⟩)
            yielding _ (facts.parkRace m raceId yielding race f ready held raceFound found)
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact held
    · rename_i g found
      have good : G (worldOf m.state (interruptRecord interp who extra g).1.id)
          (interruptRecord interp who extra g).1.id (interruptRecord interp who extra g).1.frame := by
        rw [StackLedger.interruptRecord_key]
        exact facts.interruption m.state _ g (held.found found)
      generalize interruptRecord interp who extra g = pair at good ⊢
      obtain ⟨next, applyNow⟩ := pair
      exact held.update_emit next good _
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact held
    · rename_i f found
      exact Flows.settle_one facts.interruption _ rest held _ yielding _
        (facts.afterInterrupt m host yielding kind f ready held found)
  | raceCancel raceId host yielding remaining visited =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · split
        · exact held
        · exact held
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · refine Flows.modify ?_ child _ (fun _ => rfl) (fun _ => rfl)
        refine Flows.modify held parent _ ?_ ?_
        · exact fun _ => rfl
        · exact fun _ => rfl
  | observe id exit observer =>
    simp only [driveStep]
    have kept := Flows.fireObserver interp facts.interruption facts.drop id exit (m, []) observer held
    generalize Machine.fireObserver interp id exit (m, []) observer = pair at kept ⊢
    obtain ⟨changed, nested⟩ := pair
    exact kept
  | exitDone id =>
    simp only [driveStep]
    split
    · exact held
    · rename_i f found
      exact held.update _ (facts.cleared m.state f (held.found found))
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact held
    · rename_i f found
      exact Flows.settle_one facts.interruption _ rest held _ yielding _
        (facts.closePar m host yielding fibers f ready held found)
  | link mode scope target who extra =>
    simp only [driveStep]
    have kept := Flows.linkScope interp facts.interruption facts.link m mode scope target who extra held
    generalize Machine.linkScope interp m mode scope target who extra = pair at kept ⊢
    obtain ⟨changed, nested⟩ := pair
    exact kept
  | finish id exit =>
    simp only [driveStep]
    split
    · exact held
    · rename_i f found
      have kept := Flows.exitFiber interp m {f with running := false} exit held
        (fun runs => facts.exitChildren m id exit f ready held found runs)
        (facts.publish m.state f (held.found found))
        (facts.cleared m.state {f with frame := {f.frame with deferredInterrupt := false}}
          (facts.publish m.state f (held.found found)))
      generalize Machine.exitFiber interp m {f with running := false} exit = pair at kept ⊢
      obtain ⟨changed, nested⟩ := pair
      exact kept
  | drainDue =>
    simp only [driveStep]
    exact Flows.drainOwed _ (held.state _ (facts.due m)) _
  | wake list phase =>
    simp only [driveStep]
    exact held.state _ (facts.wake m list phase)

end Commands

/-! ## The producer -/

section Producer

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable [FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α)
  (FrameEvent ν σ β ε δ ι α)]
variable {W : Type w} {World : Type w'}
variable {o : Effect4.Laws.Effects.WorldOrder W} {interp : RunInterp ν σ β ε δ ι α χ St}
variable {J : W → RunMachine ν σ β ε δ ι α χ St → Prop}
variable {I : W → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) → Prop}
variable {O : W → RunMachine ν σ β ε δ ι α χ St → List (Machine.Task ν σ β ε δ ι α) → Prop}
variable {A : W → RunMachine ν σ β ε δ ι α χ St → RunDecision ν σ β ε δ ι α → Prop}

/-- **The local facts of the producer.** What the base invariant gives at a command (`Ready`), the
commands' local facts, the store facts of the outside edits, and a prepared reply's resume. -/
structure Local (interp : RunInterp ν σ β ε δ ι α χ St)
    (J : W → RunMachine ν σ β ε δ ι α χ St → Prop)
    (I : W → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) → Prop)
    (O : W → RunMachine ν σ β ε δ ι α χ St → List (Machine.Task ν σ β ε δ ι α) → Prop)
    (A : W → RunMachine ν σ β ε δ ι α χ St → RunDecision ν σ β ε δ ι α → Prop)
    (Ready : RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop)
    (G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop) (worldOf : St → FiberId → World) :
    Prop where
  ready : ∀ ts w m c rest, m.stuck = none → Lift.Guarded J I O ts w m (c :: rest) → Ready m c
  commands : Commands interp Ready G worldOf
  outside : OutsideEdits interp G worldOf
  answer : ∀ w m id token value, J w m → m.stuck = none → A w m (.answerAsync id token value) →
    Ready {m with state := (prepareAsyncAnswer interp m id token value).1}
      (.resume id token (prepareAsyncAnswer interp m id token value).2)

/-- **The producer**: a decision lift of the base invariant, the flow carried beside it. Every
decision keeps the flow when its admission holds (`Lift.stepDecisionState_lift`). Placement: the
proposed claim `answer-flow-history`, role preservation; reach: every interpreter, base lift and
flow predicate; it establishes no answer class of a program and no progress. -/
theorem Local.decision_lift (base : Lift.DecisionLift o interp J I O A)
    {Ready : RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop}
    {G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop} {worldOf : St → FiberId → World}
    (facts : Local interp J I O A Ready G worldOf) :
    Lift.DecisionLift o interp (fun w m => J w m ∧ Flows G worldOf m) I O A :=
  base.withMachineFact (Flows G worldOf)
    (fun ts w m c rest running guarded held =>
      facts.commands.step m c rest (facts.ready ts w m c rest running guarded) held)
    (facts.outside.machineEdits facts.commands.interruption)
    (fun w m id token value invariant held running admitted =>
      facts.commands.step _ _ [Cmd.drainDue] (facts.answer w m id token value invariant running admitted)
        (held.state _ (facts.outside.prepare m id token value)))

end Producer


/-! ## The answer-flow instance

The flow of answer classes is one predicate `G`: a fiber's current code and saved frames compose, at
the world it reads, into the class its exit answers (`FamilyResult`, over an interpreter-free saved
edge). Its local facts that read no program are proved here once: a write of the interrupt fields
keeps the flow, and a code installed as the current one keeps it when it answers each class the old
code answers. -/

section Instance

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable {World Kind : Type w}

/-- **The answer flow of a frame**: its current code at some class that its saved frames carry to
the class its fiber's exit answers. -/
def FrameFlow (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop) (outputOf : FiberId → Kind)
    (world : World) (id : FiberId) (frame : FrameFiber ν σ β ε δ ι α) : Prop :=
  FamilyResult model Edge world (outputOf id) frame.current frame.stack

variable {model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind}
variable {Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop} {outputOf : FiberId → Kind}

/-- A frame write that keeps the current code and the saved frames keeps the flow: the interrupt
fields and the deferred flag are outside it. Consumers: the `publish` fact and the interrupt fact. -/
theorem FrameFlow.fields {world : World} {id : FiberId} {frame next : FrameFiber ν σ β ε δ ι α}
    (held : FrameFlow model Edge outputOf world id frame) (current : next.current = frame.current)
    (stack : next.stack = frame.stack) : FrameFlow model Edge outputOf world id next := by
  unfold FrameFlow at held ⊢
  rw [current, stack]
  exact held

/-- Replacing the current code by one that answers every class the old code answers keeps the
flow. Consumers: the reply, race-settlement and await facts of an instance. -/
theorem FrameFlow.replace {world : World} {id : FiberId} {frame : FrameFiber ν σ β ε δ ι α}
    (held : FrameFlow model Edge outputOf world id frame) (code : Prim ν σ β ε δ ι α)
    (answers : ∀ kind, model.code world kind frame.current → model.code world kind code) :
    FrameFlow model Edge outputOf world id {frame with current := code} := by
  obtain ⟨input, current, path⟩ := held
  exact ⟨input, answers input current, path⟩

end Instance

end Effect4.Machine.AnswerFlow
