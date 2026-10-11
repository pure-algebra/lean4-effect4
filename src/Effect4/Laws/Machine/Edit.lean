import Effect4.Machine.Fibers
import Effect4.Laws.Auto.RuleSets

/-!
# Primitive machine edits and their field footprint

Concept: reactive-scheduling, R11, the machine part of evaluation-moves.
Question: machine-edits supplies the field agreement used by machine invariants.
Reach: every primitive edit at every generic machine, outside its one declared write.
Consumers: Keeps field rows and Edits fiber, state, and trace adapters.
Payload validity still requires the existing actual-prefix facts.
This establishes no source admission, progress, or outside-runtime agreement.
-/
set_option autoImplicit false
namespace Effect4.Machine
universe u v

/-- The existing record fields, without a second field-value carrier. -/
inductive MachineField where
  | fibers | races | nextId | nextToken | nextRace | middlewareInstalled | armed | state | trace | stuck | forks
  deriving DecidableEq

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-- Agreement compares one existing projection at its actual type. -/
def MachineField.Agrees (field : MachineField)
    (before after : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop :=
  match field with
  | .fibers => after.fibers = before.fibers
  | .races => after.races = before.races
  | .nextId => after.nextId = before.nextId
  | .nextToken => after.nextToken = before.nextToken
  | .nextRace => after.nextRace = before.nextRace
  | .middlewareInstalled => after.middlewareInstalled = before.middlewareInstalled
  | .armed => after.armed = before.armed
  | .state => after.state = before.state
  | .trace => after.trace = before.trace
  | .stuck => after.stuck = before.stuck
  | .forks => after.forks = before.forks

/-- Primitive machine writes, with first-order payloads. Code and frame sorts stay generic. -/
inductive Edit (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v))
    (κ φ η : Type (max u v)) : Type (max u v) where
  | update (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
  | emit (events : List (RunEvent ν σ β ε δ ι α χ κ η))
  | arm (owner : FiberId)
  | disarm (owner : FiberId)
  | halt (why : Stuck)
  | updateRace (race : Race ν σ β ε δ ι α κ)
  | appendFiber (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
  | appendRace (race : Race ν σ β ε δ ι α κ)
  | bumpId
  | bumpToken
  | bumpRace
  | addFork (record : ForkRecord)
  | setState (state : St)
  | setMiddleware (installed : Bool)
  | observe (target : FiberId) (observer : Observer)
  | dropToken (token : Nat)

namespace Edit

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-- Interpret a primitive write. No stored payload is a Lean function. -/
def apply : Edit ν σ β ε δ ι α χ St κ φ η →
    RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η
  | .update fiber, m => m.update fiber
  | .emit events, m => m.emit events
  | .arm owner, m => m.arm owner
  | .disarm owner, m => m.disarm owner
  | .halt why, m => m.halt why
  | .updateRace race, m => m.updateRace race
  | .appendFiber fiber, m => {m with fibers := m.fibers ++ [fiber]}
  | .appendRace race, m => {m with races := m.races ++ [race]}
  | .bumpId, m => {m with nextId := m.nextId + 1}
  | .bumpToken, m => {m with nextToken := m.nextToken + 1}
  | .bumpRace, m => {m with nextRace := m.nextRace + 1}
  | .addFork record, m => {m with forks := m.forks ++ [record]}
  | .setState state, m => {m with state := state}
  | .setMiddleware installed, m => {m with middlewareInstalled := installed}
  | .observe target observer, m => m.modify target fun f => {f with observers := f.observers ++ [observer]}
  | .dropToken token, m => m.dropToken token

/-- Each edit declares the one machine field it may write. -/
def writes : Edit ν σ β ε δ ι α χ St κ φ η → MachineField
  | .update _ | .appendFiber _ | .observe _ _ | .dropToken _ => .fibers
  | .updateRace _ | .appendRace _ => .races
  | .bumpId => .nextId
  | .bumpToken => .nextToken
  | .bumpRace => .nextRace
  | .arm _ | .disarm _ => .armed
  | .setMiddleware _ => .middlewareInstalled
  | .setState _ => .state
  | .emit _ => .trace
  | .halt _ => .stuck
  | .addFork _ => .forks

/-- A passive record classification, with no evaluator or invariant census. -/
theorem frame (edit : Edit ν σ β ε δ ι α χ St κ φ η) (field : MachineField)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (miss : field ≠ writes edit) :
    field.Agrees m (edit.apply m) := by
  fun_cases writes edit <;> cases field
  all_goals dsimp only [writes] at miss
  all_goals aesop (add simp [MachineField.Agrees, Edit.apply, RunMachine.update, RunMachine.updateRace,
    RunMachine.emit, RunMachine.arm, RunMachine.disarm, RunMachine.halt, RunMachine.modify, RunMachine.dropToken])

end Edit
end Effect4.Machine
