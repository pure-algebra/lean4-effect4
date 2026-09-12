import Effect4.Laws.Program.Guard

/-! DI-68: an outstanding host request persists through every raw decision
except its matching answer, unless its fiber is interrupted or has exited.
Reachability fixes the program, table, compile budget, choices, and initial
answers while allowing an arbitrary command budget at each prefix step. -/
set_option autoImplicit false

namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program

/-- The owner-approved interruption observation includes a recorded or deferred
interrupt and an already-published exit. -/
abbrev Interrupted (f : Guard.NFiber) : Prop := Guard.Interrupted f

variable {p : Api.Program} {table : RowTable} {cf : Nat} {choices : List Bool}
  {answers : List (Completion Val Err Defect FiberId Ann)} {m : Api.Machine}
  {fuel : Nat} {d : Api.Decision} {key : HostProtocol.Key} {r : NativeOp × Val}

/-- DI-68, reachable-machine amendment: all nonmatching raw decisions are
allowed. The interruption alternative is observed after the step. -/
theorem guard_persists
    (reachable : Guard.Reachable p table cf choices answers m)
    (request : Api.requestOf m key.fiber key.token = some r)
    (other : ∀ answer, d ≠ .answerAsync key.fiber key.token answer) :
    let after := Program.steppedBy p fuel table m d
    Api.requestOf after key.fiber key.token = some r ∨
      ∃ f, after.fiber? key.fiber = some f ∧ Interrupted f :=
  Guard.requestOrInterrupted_steppedBy p table fuel m d key.fiber key.token r
    (Guard.guardState_reachable p table cf choices answers m reachable) request other

/-- With one starting fiber, no cancellation, and no answer to the protected
key, the request is unchanged. A pre-existing interrupt cause is permitted. -/
theorem guard_persists_single {f : Guard.NFiber}
    (reachable : Guard.Reachable p table cf choices answers m)
    (single : m.fibers = [f])
    (request : Api.requestOf m key.fiber key.token = some r)
    (other : ∀ answer, d ≠ .answerAsync key.fiber key.token answer)
    (noCancel : ∀ who annotations target, d ≠ .interruptFrom who annotations target) :
    Api.requestOf (Program.steppedBy p fuel table m d) key.fiber key.token = some r :=
  Guard.SingleGuard.requestOf_singleton_steppedBy p table fuel
    (Guard.guardState_reachable p table cf choices answers m reachable) single request d
    ((Guard.SingleGuard.noCancel_iff d).mpr noCancel) other

/-- The single-fiber equality extends across a finite tape prefix. Each entry
retains its own command budget; only the initial machine must be a singleton. -/
theorem guard_persists_single_tape {f : Guard.NFiber}
    (reachable : Guard.Reachable p table cf choices answers m)
    (single : m.fibers = [f])
    (request : Api.requestOf m key.fiber key.token = some r)
    (history : List (Nat × Api.Decision))
    (other : ∀ entry ∈ history, ∀ answer, entry.2 ≠ .answerAsync key.fiber key.token answer)
    (noCancel : ∀ entry ∈ history, ∀ who annotations target,
      entry.2 ≠ .interruptFrom who annotations target) :
    Api.requestOf (Guard.executePrefix p table m history) key.fiber key.token = some r :=
  Guard.SingleGuard.requestOf_singleton_executePrefix p table
    (Guard.guardState_reachable p table cf choices answers m reachable) single request history
    (fun entry member => ⟨(Guard.SingleGuard.noCancel_iff entry.2).mpr (noCancel entry member),
      other entry member⟩)

#print axioms guard_persists
#print axioms guard_persists_single
#print axioms guard_persists_single_tape
end Effect4.Api
