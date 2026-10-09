module

/-! Scalar bookkeeping for finite natural counts, including zero.
The source is `vendor/effect-4.0.1/src/PartitionedSemaphore.ts`.
`Counts` is a scalar subrecord, without request identities or partition queues.
No definition reads Step syntax or its evaluator.
Placement: `partitioned-semaphore-bookkeeping`, translation-simulation, R10. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PartitionedSemaphore

namespace Model
/-- Scalar projection of latest's finite natural-count bookkeeping. -/
structure Counts where
  capacity : Nat
  available : Nat
  waiting : Nat
  deriving DecidableEq, Repr

/-- Latest PartitionedSemaphore.ts:135-136, with capacity restricted to Nat. -/
def initial (capacity : Nat) : Counts := ⟨capacity, capacity, 0⟩

/-- Latest PartitionedSemaphore.ts:284 reads totalPermits. -/
def available (s : Counts) : Nat := s.available

/-- Latest PartitionedSemaphore.ts:268-278; natural counts omit negative requests. -/
def tryTake (s : Counts) (requested : Nat) : Bool × Counts :=
  if requested = 0 then (true, s)
  else if decide (s.capacity < requested) || decide (s.available < requested) then (false, s)
  else (true, { s with available := s.available - requested })

/-- Latest PartitionedSemaphore.ts:207-211, only inside the insufficient-availability branch. -/
def reserve (s : Counts) (requested : Nat) : Nat × Counts :=
  let needed := requested - s.available
  (needed, { s with available := 0, waiting := s.waiting + needed })
end Model

end Effect4.PartitionedSemaphore
