import Effect4.Machine.Fibers
import Effect4.Laws.Auto.RuleSets

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Consumer: source-owned and pending-initialization dispatcher reply certificates.
The existing insertion proof is parametric in the task predicate.
-/
set_option autoImplicit false
namespace Effect4.Machine.DispatcherPredicate
open Effect4 Effect4.Machine
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {κ : Type (max u v)}

/-- A task list carries the supplied local task assertion. -/
def Tasks (P : Task ν σ β ε δ ι α κ → Prop) (tasks : List (Task ν σ β ε δ ι α κ)) : Prop :=
  ∀ task ∈ tasks, P task

/-- Every dispatcher bucket carries the supplied local task assertion. -/
def All (P : Task ν σ β ε δ ι α κ → Prop) (dispatcher : Dispatcher ν σ β ε δ ι α κ) : Prop :=
  ∀ bucket ∈ dispatcher.buckets, Tasks P bucket.tasks

/-- Insertion retains the new task assertion and every old bucket assertion. -/
theorem insert (P : Task ν σ β ε δ ι α κ → Prop) (priority : Nat) (task : Task ν σ β ε δ ι α κ)
    (buckets : List (Bucket ν σ β ε δ ι α κ)) (owned : ∀ bucket ∈ buckets, Tasks P bucket.tasks)
    (new : P task) : ∀ bucket ∈ Dispatcher.insert priority task buckets, Tasks P bucket.tasks := by
  induction buckets with
  | nil => aesop (add norm simp [Dispatcher.insert, Tasks, List.mem_cons])
  | cons bucket rest ih =>
    have first := owned bucket (.head _)
    have tail : ∀ bucket ∈ rest, Tasks P bucket.tasks := fun b hb => owned b (.tail _ hb)
    have kept := ih tail
    unfold Dispatcher.insert
    repeat' split
    all_goals aesop (add norm simp [Tasks, List.mem_cons, List.mem_append])

/-- Enqueue changes no old task assertion. -/
theorem enqueue (P : Task ν σ β ε δ ι α κ → Prop) (dispatcher : Dispatcher ν σ β ε δ ι α κ)
    (priority : Nat) (task : Task ν σ β ε δ ι α κ) (owned : All P dispatcher) (new : P task) :
    All P (dispatcher.enqueue priority task) := insert P priority task dispatcher.buckets owned new
/-- Draining retains every actual task assertion and leaves an empty dispatcher. -/
theorem drain (P : Task ν σ β ε δ ι α κ → Prop) (dispatcher : Dispatcher ν σ β ε δ ι α κ)
    (owned : All P dispatcher) : Tasks P dispatcher.drain.1 ∧ All P dispatcher.drain.2 := by
  constructor
  · intro task member
    obtain ⟨tasks, present, member⟩ := List.mem_flatten.mp member
    obtain ⟨bucket, present, same⟩ := List.mem_map.mp present
    rw [← same] at member
    exact owned bucket present task member
  · intro bucket member
    exact (List.not_mem_nil member).elim

end Effect4.Machine.DispatcherPredicate
