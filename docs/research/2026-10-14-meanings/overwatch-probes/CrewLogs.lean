import Test.Dogfood.Scenario.Workers.Assertions
import Test.Dogfood.Scenario.QueueWorkers.Assertions

/-!
# Overwatch probe: the two log goals are one history statement

Concept: scope-lifetime-finalization R11, at most once per registration counted by identity.
Question: `Workers.Assertions.logs_step` and `QueueWorkers.Assertions.logs_history`. Consumer: the
two crews' `releases_once` clauses, through their goals.

`CrewLogHistory` states the log clause once, over a crew's identities, its acquisition paths and
its log cell. The probe checks that both planned goals follow from it at their crews, with the
goals' statements unchanged. The Workers goal is its step form, through the proved
`Workers.Assertions.history_step`.

Reach. Every job total, compile budget, built crew and admitted history.
Not established. `CrewLogHistory` itself: it is the one statement that the generic proof over
`AnswerSlots.Typed.Spec` owes (`CrewSpec.workers` shows that the first crew is a `Spec`).
-/

set_option autoImplicit false

namespace Overwatch.CrewLogs
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario

/-- The entries of a reference cell that holds a list. -/
def logAt (cell : Nat) (m : NativeMachine) : List Val :=
  match (m.state.refs[cell]? : Option Val) with
  | some (.list values) => values
  | _ => []

/-- The log clause of a crew: each entry is an identity, and each identity's entries are at most
its release starts, counted by its acquisition path. -/
def CrewLogs (identities : List Nat) (acquirePath : Nat → List Nat) (cell : Nat)
    (m : NativeMachine) : Prop :=
  (∀ value ∈ logAt cell m, ∃ i ∈ identities, value = .nat i) ∧
    ∀ i ∈ identities, (logAt cell m).count (.nat i) ≤
      m.trace.countP (ReleaseTrace.releaseAt (acquirePath i))

/-- The one statement: the log clause along every admitted history of a built crew. -/
def CrewLogHistory (identities : List Nat) (acquirePath : Nat → List Nat) (cell : Nat)
    (b : Api.Built) : Prop :=
  ∀ compileFuel m, Run.HistoryOf b compileFuel m → CrewLogs identities acquirePath cell m

/-- `Workers.Assertions.logs_step`, from the one statement at the first crew. -/
theorem workers_logs_step
    (crew : ∀ total b, Api.Author.build (Workers.crew total) = .ok b →
      CrewLogHistory [1, 2] Programs.crewAcquire 1 b) :
    ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision),
      Api.Author.build (Workers.crew total) = .ok b → Workers.Assertions.Holds b cf m →
      Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2 →
      Workers.Assertions.LogDebits (Run.stepBy b m x) := by
  intro total cf b m x built held accepted
  have logs := crew total b built cf (Run.stepBy b m x)
    (Workers.Assertions.history_step b cf m x held.history accepted)
  refine ⟨fun value member => ?_, logs.2⟩
  obtain ⟨i, inside, rfl⟩ := logs.1 value member
  rcases List.mem_cons.mp inside with rfl | tail
  · exact .inl rfl
  · rw [List.mem_singleton.mp tail]
    exact .inr rfl

/-- `QueueWorkers.Assertions.logs_history`, the one statement at the queue crew. -/
theorem queue_logs_history
    (crew : ∀ total b, Api.Author.build (QueueWorkers.crew total) = .ok b →
      CrewLogHistory [1, 2, 3] Programs.queueAcquire 2 b)
    (total compileFuel : Nat) (b : Api.Built) (machine : NativeMachine)
    (built : Api.Author.build (QueueWorkers.crew total) = .ok b)
    (history : Run.HistoryOf b compileFuel machine) :
    (∀ value ∈ QueueWorkers.Assertions.log machine, ∃ i ∈ [1, 2, 3], value = .nat i) ∧
      ∀ i ∈ [1, 2, 3], (QueueWorkers.Assertions.log machine).count (.nat i) ≤
        machine.trace.countP (ReleaseTrace.releaseAt (QueueWorkers.Assertions.acquirePath i)) :=
  crew total b built compileFuel machine history

end Overwatch.CrewLogs
