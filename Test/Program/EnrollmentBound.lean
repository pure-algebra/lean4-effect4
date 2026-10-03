import Test.Program.RegistrationColumn
import Effect4.Laws.Program.Typed.Commands.Observe

/-!
# Test.Program.EnrollmentBound — weak queued-child allocation bound

Placement: semantics Concept 4, scheduler preservation and step invariant lifting;
`launch_preserves` and the existing `enrollRace_preserves`. This battery checks the
lead coordinator's row 134 (e) weak-bound clarification (ratified by the owner, 2026-10-02):
an enrollment child is below `nextId`, while an absent old child remains inert
(`E4-TYPED-CE-032`). It leaves the current successful-lookup column test intact.

The future-ID setup is copied from the checked `launch-audit/Launch.candidate.lean` at
4c219956; that retained falsifier and its old predicate are not imported or edited. Its exact
machine and queue are now rejected at `QueueOk.enroll`. The positive case copies only the
checked RegistrationColumn fixture's allocation counter to 2, leaving child 1 absent, constructs
full `ConfigTyped`, and invokes the actual `enrollRace_preserves`. The incompatible-present
case uses the future-ID fixture's real child 1 against race 0: its bound passes, its string
column does not fit the race's number column.

These are constructed-configuration controls, not claims that their inputs are reachable.
They prove no launch preservation theorem, capstone, progress, fairness or external/target
agreement. They serve the invariant boundary on the M5 -> M6 -> M7 spine.
-/

set_option autoImplicit false

namespace Test.Program.EnrollmentBound
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World
abbrev RaceR := Effect4.Program.Typed.RRace

namespace Future

def rootProgram : NativeEff := .succeed (.lit (.nat 0))
def natTy : EffTy := EffTy.pure .nat
def stringTy : EffTy := EffTy.pure .string
def other : FiberId := ⟨1⟩
def fresh : FiberId := ⟨2⟩
def marker (r : Nat) : RProgram := .vis (.inr (.raceRegister r)) Effects.Program.pure
def entrant : RProgram := .pure (.success (.nat 0))
def host (id : FiberId) (r : Nat) : RFiber :=
  { RunFiber.make id (marker r) true (stores.budgetOf emptyCtx) emptyCtx with running := true }
def fiber0 := host Api.root 0
def fiber1 := host other 1

def race0 : RaceR :=
  { id := 0, host := Api.root, token := 0, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [entrant], registering := true }
def race1 : RaceR :=
  { id := 1, host := other, token := 1, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [], registering := true }
def machine : RState :=
  { loadR rootProgram 20 20 with
    fibers := [fiber0, fiber1], races := [race0, race1],
    nextId := 2, nextToken := 2, nextRace := 2 }
def world : W :=
  { initialWorld natTy with
    ids := [Api.root, other]
    Γ := fun id => if id = Api.root then some natTy else if id = other then some stringTy else none
    Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy
      else if id = other ∧ t = 1 then some stringTy else none }
def rest : List RCmd := [.enrollRace 1 fresh, .registrationDone 0 false, .registrationDone 1 false]
def commands : List RCmd := .launch 0 :: rest

/-- The exact queued child in the checked falsifier equals the allocator's next ID. -/
theorem at_counter : fresh.value = machine.nextId := rfl

/-- The new weak bound rejects the precise local enrollment that previously became active
when launch allocated child 2. No type incompatibility is needed for this rejection. -/
theorem enrollment_refused : ¬ EnrollRaceOk (rootProgram : ProgramSource) world machine 1 fresh := by
  intro enrolled
  have bound : 2 < 2 := enrolled.1
  exact Nat.lt_irrefl 2 bound

/-- The exact old full queue is rejected through its enrollment premise. -/
theorem config_refused : ¬ ConfigTyped (rootProgram : ProgramSource) natTy world machine commands := by
  intro typed
  have member : Cmd.enrollRace 1 fresh ∈ commands :=
    List.mem_cons_of_mem _ List.mem_cons_self
  exact enrollment_refused (typed.queue.enroll 1 fresh member)

end Future

namespace MissingOld

abbrev rootProgram := Test.Program.RegistrationColumn.rootProgram
abbrev natTy := Test.Program.RegistrationColumn.natTy
abbrev world := Test.Program.RegistrationColumn.world
abbrev fiber := Test.Program.RegistrationColumn.fiber
abbrev race := Test.Program.RegistrationColumn.race

def machine : RState := { Test.Program.RegistrationColumn.machine with nextId := 2 }
def child : FiberId := ⟨1⟩
def rest : List RCmd := [.registrationDone 0 false]
def commands : List RCmd := .enrollRace 0 child :: rest

/-- The sole machine change from RegistrationColumn is allocator headroom. -/
theorem nextId_grows : Test.Program.RegistrationColumn.machine.nextId ≤ machine.nextId := by
  decide +kernel

/-- The control is deliberately absent, but strictly below the next allocation. -/
theorem absent_below : machine.fiber? child = none ∧ child.value < machine.nextId :=
  ⟨rfl, Nat.one_lt_two⟩

/-- The weak bound retains the original predicate's missing-child arm. -/
theorem enrollment_ok : EnrollRaceOk (rootProgram : ProgramSource) world machine 0 child := by
  exact ⟨absent_below.2, trivial⟩

/-- Raising only the allocation counter retains the fixture's scheduler clauses. -/
theorem scheduler : SchedulerState machine := by
  have old := Test.Program.RegistrationColumn.typedState.2.2.2.1
  exact
    { fiberIds := old.fiberIds
      fibersBelow := fun f hf => Nat.lt_of_lt_of_le (old.fibersBelow f hf) nextId_grows
      raceIds := old.raceIds
      racesBelow := old.racesBelow
      raceHosts := old.raceHosts
      keysBelow := old.keysBelow
      requestsBelow := old.requestsBelow
      requestsOwned := old.requestsOwned
      pendingShape := old.pendingShape
      parkedIdle := old.parkedIdle
      parkedBelow := old.parkedBelow
      exited := old.exited
      exitedStack := old.exitedStack
      deferredCause := old.deferredCause
      raceObservers := old.raceObservers
      liveBelow := fun r race hr id hi => Nat.lt_of_lt_of_le (old.liveBelow r race hr id hi) nextId_grows
      targetsBelow := fun f hf p hp id hi => Nat.lt_of_lt_of_le (old.targetsBelow f hf p hp id hi) nextId_grows
      observersBelow := fun f hf o ho k hk => Nat.lt_of_lt_of_le (old.observersBelow f hf o ho k hk) nextId_grows }

/-- All columns, including the current timer/waiter clauses, are the checked fixture's;
only the scheduler's allocation bound changes. The structure clauses read no allocation
counter, so each is the fixture's own fields at the raised machine. -/
theorem typedState : TypedState (rootProgram : ProgramSource) natTy world machine := by
  have old := Test.Program.RegistrationColumn.typedState
  refine ⟨{ old.1 with }, { old.2.1 with },
    activeDelivery_races (m := Test.Program.RegistrationColumn.machine) rfl
      (racesKept_of_eq fun _ => rfl) old.2.2.1, scheduler,
    { old.2.2.2.2.1 with observers := ?_ },
    registrationState_races (m := Test.Program.RegistrationColumn.machine) rfl
      (racesKept_of_eq fun _ => rfl) old.2.2.2.2.2⟩
  intro f hf o ho
  rw [Test.Program.RegistrationColumn.member hf] at ho
  cases ho

/-- The complete machine premise consumed by the absent-old configuration control. -/
theorem machine_typed : MachineTyped (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩, rfl⟩
  intro f hf _ idle
  rw [Test.Program.RegistrationColumn.member hf] at idle
  cases idle

/-- The pending registration tail is typed at the raised allocator. It contains no enrollment. -/
theorem tail_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine rest := by
  change ConfigTyped (rootProgram : ProgramSource) natTy world machine [.registrationDone 0 false]
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;> (rw [List.mem_singleton] at r; cases r)
  · refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨race, fiber, rfl, rfl, rfl, rfl, rfl⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro k member
      cases member
    · intro fiber token request _ member
      cases member
    · intro source exit observer member
      rw [List.mem_singleton] at member
      cases member
    · intro race child member
      rw [List.mem_singleton] at member
      cases member
    · intro host yielding race member
      rw [List.mem_singleton] at member
      cases member
    · intro mode scope target interruptor extra member
      rw [List.mem_singleton] at member
      cases member
    · intro source exit observer member
      rw [List.mem_singleton] at member
      cases member

/-- A complete input to the actual enrollment command; no child-presence hypothesis is used. -/
theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine commands := by
  refine ⟨tail_typed.machine,
    readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) tail_typed.code,
    queueOk_cons ?_ tail_typed.queue⟩
  refine
    { payload := trivial
      authority := ⟨race, rfl, fiber, rfl, rfl, rfl⟩
      delivery := trivial
      owner := fun _ h => nomatch h
      tail := ⟨false, List.mem_singleton_self _⟩
      keysBelow := fun _ h => nomatch h
      keysFree := fun _ _ _ _ h => nomatch h
      observer := fun _ _ _ h => nomatch h
      enroll := ?_
      noRace := fun _ _ _ h => nomatch h
      link := fun _ _ _ _ _ h => nomatch h
      raceObservers := fun _ _ _ h => nomatch h }
  intro r c same
  cases same
  exact enrollment_ok

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.enrollRace 0 child) rest

/-- The actual missing-old transition leaves the machine and remaining queue exactly alone. -/
theorem inert : result = (machine, rest) := rfl

/-- The existing general command theorem admits this absent-old input and types its result. -/
theorem result_typed : ∃ w', world.leHost w' ∧
    ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 := by
  exact enrollRace_preserves (rootProgram : ProgramSource) natTy 0 child
    world machine rest rfl config_typed

end MissingOld

namespace IncompatiblePresent

/-- Unlike Future.fresh, this target already exists and passes the new bound. -/
theorem present_below : Future.machine.fiber? Future.other = some Future.fiber1 ∧
    Future.other.value < Future.machine.nextId := ⟨rfl, Nat.one_lt_two⟩

/-- The bound alone is insufficient: child 1's string declaration fails race 0's number column.
This isolates the unchanged successful-lookup compatibility clause. -/
theorem enrollment_refused :
    ¬ EnrollRaceOk (Future.rootProgram : ProgramSource) Future.world Future.machine 0 Future.other := by
  intro enrolled
  have compatibility : ∃ resultTy,
      RacePayload (Future.rootProgram : ProgramSource) Future.world Future.race0 resultTy ∧
      FiberColumnsBelow Future.world Future.fiber1.id resultTy.answer resultTy.error := enrolled.2
  obtain ⟨resultTy, payload, cols⟩ := compatibility
  have pinned : some Future.natTy = some resultTy := payload.token
  cases pinned
  obtain ⟨childTy, declared, subA, _⟩ := cols
  have pinnedChild : some Future.stringTy = some childTy := declared
  cases pinnedChild
  exact (by decide +kernel : Ty.subN Ty.string Ty.nat ≠ true) subA

end IncompatiblePresent

namespace ObserveSource

/-- Decisions row 189 (`E4-TYPED-CE-035`), beside row 134 (e)'s enrollment bound: a
queued `observe` whose source is the next fiber id is refused at every world, whatever its observer and exit (the checked
falsifier `witnesses/LaunchQueuedObserve.lean` queued exactly this with an `untrackChild`). -/
theorem future_refused (w : W) (q : List RCmd) :
    ¬ QueueOk (Test.Program.RegistrationColumn.rootProgram : ProgramSource) w
      Test.Program.RegistrationColumn.machine
      (.observe ⟨1⟩ (.success (.str "x")) (.untrackChild Api.root) :: q) := by
  intro queue
  exact Nat.lt_irrefl 1 (queue.observer _ _ _ List.mem_cons_self).1

abbrev rootProgram := Test.Program.RegistrationColumn.rootProgram
abbrev natTy := Test.Program.RegistrationColumn.natTy
abbrev world := Test.Program.RegistrationColumn.world

def source : FiberId := ⟨1⟩
def obs : RCmd := .observe source (.success (.str "x")) (.untrackChild Api.root)
def commands : List RCmd := obs :: MissingOld.rest

/-- A missing old source (below `nextId`, undeclared) stays admitted with any exit: the payload
clause is vacuous at an undeclared source and the bound holds. -/
theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world MissingOld.machine
    commands := by
  refine ⟨MissingOld.tail_typed.machine,
    readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) MissingOld.tail_typed.code,
    queueOk_cons ?_ MissingOld.tail_typed.queue⟩
  refine
    { payload := fun ty declared => by
        change (initialWorld natTy).Γ source = some ty at declared
        cases declared
      authority := trivial
      delivery := trivial
      owner := fun _ h => nomatch h
      tail := trivial
      keysBelow := fun _ h => nomatch h
      keysFree := fun _ _ _ _ h => nomatch h
      observer := ?_
      enroll := fun _ _ h => nomatch h
      noRace := fun _ _ _ h => nomatch h
      link := fun _ _ _ _ _ h => nomatch h
      raceObservers := ?_ }
  · intro src e o same
    cases same
    exact ⟨Nat.one_lt_two, trivial⟩
  · intro src e o same _ _ _ hk
    cases same
    cases hk

/-- The existing general command theorem types the absent-old observe's step. -/
theorem result_typed : ∃ w', world.leHost w' ∧ ConfigTyped (rootProgram : ProgramSource) natTy w'
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) MissingOld.machine obs MissingOld.rest).1
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) MissingOld.machine obs MissingOld.rest).2 :=
  observe_preserves (rootProgram : ProgramSource) natTy source _ _ world MissingOld.machine
    MissingOld.rest rfl config_typed

end ObserveSource

end Test.Program.EnrollmentBound
