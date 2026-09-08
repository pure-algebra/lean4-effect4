import Effect4.Laws.Machine.Scheduling
import Effect4.Machine.Stores

/-! LIVE/fair: two armed owners, insufficient fuel, and an unknown owner.
These finite checks accompany the universal conditional `flush_fair` theorem. -/

set_option autoImplicit false

namespace Test.Runtime.SchedulingContract

open Effect4 Effect4.Machine Effect4.Machine.Scheduling

abbrev M := RunMachine Name Thunk Val Err Defect FiberId Ann Ctx Stores
abbrev F := RunFiber Name Thunk Val Err Defect FiberId Ann Ctx

def ownerFiber (id : FiberId) : F :=
  { (RunFiber.make id (Prim.success (Val.nat id.value)) true (2048, false) emptyCtx : F) with
    dispatcher := Dispatcher.empty.enqueue 0 (Task.start id) }

def twoOwners : M :=
  { (RunMachine.empty Stores.empty : M) with
    fibers := [ownerFiber ⟨0⟩, ownerFiber ⟨1⟩], nextId := 2, armed := [⟨0⟩, ⟨1⟩] }

#guard FlushReady stores 40 2 twoOwners
#guard (flushAllState stores 40 2 twoOwners).2
#guard (flushAllState stores 40 2 twoOwners).1.armed.isEmpty
#guard FiredWithin stores 40 1 twoOwners ⟨0⟩
#guard !(FiredWithin stores 40 1 twoOwners ⟨1⟩)
#guard FiredWithin stores 40 2 twoOwners ⟨1⟩

theorem both_serviced :
    ∀ owner ∈ twoOwners.armed, FiredWithin stores 40 2 twoOwners owner = true :=
  flush_fair stores 40 2 twoOwners (by decide) (by decide) (by decide)

-- E4-LIVE-CE-001: enough rounds alone cannot cross a command-fuel frontier.
#guard !(FlushReady stores 1 2 twoOwners)
#guard !(flushAllState stores 1 2 twoOwners).2
#guard (flushAllState stores 1 2 twoOwners).1.armed = [⟨1⟩]
#guard ((flushAllState stores 1 2 twoOwners).1.fiber? ⟨1⟩).map
  (fun f => f.running) = some false
#guard !(FiredWithin stores 1 2 twoOwners ⟨1⟩)

theorem round_bound_alone_false :
    ¬ (∀ fuel, ∀ owner ∈ twoOwners.armed,
      FiredWithin stores fuel twoOwners.armed.length twoOwners owner = true) := by
  intro h
  have bad := h 1 ⟨1⟩ (by decide)
  have no : FiredWithin stores 1 twoOwners.armed.length twoOwners ⟨1⟩ = false := by decide
  rw [no] at bad
  cases bad

-- E4-LIVE-CE-002: an unknown queue head cannot drain or move out of the way.
def unknownHead : M := { twoOwners with armed := [⟨7⟩, ⟨0⟩, ⟨1⟩] }
#guard !(FlushReady stores 40 3 unknownHead)
#guard (flushAllState stores 40 3 unknownHead).1.armed = unknownHead.armed
#guard !(FiredWithin stores 40 3 unknownHead ⟨0⟩)
#guard !(FiredWithin stores 40 3 unknownHead ⟨7⟩)

-- Fairness is a predicate on the supplied finite tape, not a scheduler assumption.
theorem empty_queue_empty_tape_fair :
    FairTape stores 40 (RunMachine.empty Stores.empty) [] := by
  intro pre suffix ht _ _ owner ho
  have hp : pre = [] := (List.append_eq_nil_iff.mp ht.symm).1
  subst pre
  simp [replayEval, RunMachine.empty, RunMachine.finished, ReplayResult.machine] at ho

end Test.Runtime.SchedulingContract
