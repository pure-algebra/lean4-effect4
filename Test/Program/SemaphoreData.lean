import Effect4.Laws.Library.Semaphore.Steps
import Effect4.Laws.Library.Semaphore.Typing

/-! Readers and finite controls of Semaphore's Step-data migration.
Placement: `semaphore-steps-agree` (R10), and the Step typing consumers (R4).
The checks exercise populated cells and real deferred keys, not a native host. -/
set_option autoImplicit false
namespace Test.Program.SemaphoreData
open Effect4 Effect4.Machine Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.Semaphore.Model

def table : Table := { handle := fun n => ⟨n + 10⟩, hint := fun n => ⟨n + 20⟩ }
def state : State := { permits := 3, taken := 2, next := 4, waiters := [⟨1, 2, 1⟩, ⟨2, 1, 2⟩] }

example : table.Injective := by
  intro a b same
  have indices := congrArg DeferredKey.index same
  exact Nat.add_right_cancel indices

-- The pending take removes its prior waiter, then enrolls with the supplied hint.
#guard !(Effect4.Semaphore.Data.take.eval Leaves.deferredKeys (takeInputs table state 1 2 ⟨90⟩)).1
#guard ((Effect4.Semaphore.Data.waitersF.get
  (Effect4.Semaphore.Data.take.eval Leaves.deferredKeys (takeInputs table state 1 2 ⟨90⟩)).2).map
    (fun w => DeferredKey.index w.1)) == [22, 90]
-- Withdrawal removes only the matching identity.
#guard ((Effect4.Semaphore.Data.waitersF.get
  (Effect4.Semaphore.Data.withdraw.eval Leaves.deferredKeys (withdrawInputs table state 1)).2).map
    (fun w => DeferredKey.index w.2.1)) == [12]
-- A visit skips the oversized first waiter and selects the fitting second waiter.
#guard (Effect4.Semaphore.Data.visit.eval Leaves.deferredKeys (inputsAt table state 0)).1.map
  (fun w => DeferredKey.index w.2.1) == some 12

-- An aliasing table cannot identify a model request number from handle equality.
def aliasing : Table := { handle := fun _ => ⟨0⟩, hint := fun n => ⟨n⟩ }
#guard Effect4.Schema.Model.deferredEqual Leaves.deferredKeys (aliasing.handle 1) (aliasing.handle 2)
#guard (1 : Nat) != 2

-- Reader of the independent transition connector at every populated state and injective table.
example (tb : Table) (s : State) (id n : Nat) (hint : DeferredKey) (injective : tb.Injective) :
    Effect4.Semaphore.Data.take.eval Leaves.deferredKeys (takeInputs tb s id n hint) =
      ((take s id n).2, cellC (tb.renew id hint) (take s id n).1) :=
  take_eval tb s id n hint injective
end Test.Program.SemaphoreData
