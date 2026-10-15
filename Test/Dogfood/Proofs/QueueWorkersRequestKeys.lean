import Test.Dogfood.Proofs.QueueWorkersCustodyCredits

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the request allocator's actual callback input.
A logical custody request receives its concrete deferred key from the actual native allocation.
Other allocations preserve every published request key.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersRequestKeys
open Effect4 Effect4.Machine Effect4.Program
open QueueWorkersCustody

/-- Published native request keys extend the existing custody proof world. -/
structure World where
  custody : QueueWorkersCustody.World
  keys : Nat → Option DeferredKey

/-- Published keys remain immutable while the existing request classes advance. -/
def Future (first last : World) : Prop :=
  QueueWorkersCustody.Future first.custody last.custody ∧
    ∀ token key, first.keys token = some key → last.keys token = some key

/-- The callback consumes the actual key of its still-live request. -/
def KeyAt (world : World) (token : Nat) : Val → Prop
  | .promise ⟨index⟩ => world.keys token = some ⟨index⟩ ∧ (world.custody.requests token).Pending
  | _ => False

/-- Every published request key predates the next native deferred allocation. -/
def Bound (world : World) (state : Stores) : Prop :=
  ∀ token key, world.keys token = some key → key.index < state.deferreds.cells.length

/-- Distinct logical requests have distinct native deferred keys. -/
def Unique (world : World) : Prop :=
  ∀ token other key, world.keys token = some key → world.keys other = some key → token = other

/-- The actual allocator publishes its returned key for one logical request. -/
def publish (world : World) (token : Nat) (key : DeferredKey) : World :=
  {world with keys := fun selected => if selected = token then some key else world.keys selected}

/-- Publishing a previously unallocated request preserves every old published key. -/
theorem publish_future (world : World) (token : Nat) (key : DeferredKey)
    (fresh : world.keys token = none) : Future world (publish world token key) := by
  refine ⟨QueueWorkersCustody.order.refl _, ?_⟩
  intro selected old held
  by_cases same : selected = token
  · subst selected
    rw [fresh] at held
    cases held
  · simpa only [publish, if_neg same] using held

/-- Native deferred allocation supplies one world for immutable keys and its exact classified answer. -/
theorem allocated (world : World) (token : Nat) (state after : Stores) (value : Val)
    (fresh : world.keys token = none) (pending : (world.custody.requests token).Pending)
    (bound : Bound world state) (unique : Unique world)
    (ran : syncOpStep .deferredMake state = some (after, value)) :
    let next := publish world token ⟨state.deferreds.cells.length⟩
    Future world next ∧ KeyAt next token value ∧ Bound next after ∧ Unique next := by
  rw [syncOpStep_deferredMake] at ran
  cases ran
  refine ⟨publish_future world token _ fresh, ?_, ?_, ?_⟩
  · change (if token = token then some ⟨state.deferreds.cells.length⟩ else world.keys token) =
      some ⟨state.deferreds.cells.length⟩ ∧ (world.custody.requests token).Pending
    exact ⟨if_pos rfl, pending⟩
  · intro selected key held
    change key.index < (state.deferreds.cells ++ [_]).length
    rw [List.length_append, List.length_singleton]
    by_cases same : selected = token
    · subst selected
      have equal : key = ⟨state.deferreds.cells.length⟩ := Option.some.inj (by simpa only [publish, ↓reduceIte] using held.symm)
      subst key
      change state.deferreds.cells.length < state.deferreds.cells.length + 1
      omega
    · have old : world.keys selected = some key := by simpa only [publish, if_neg same] using held
      have small := bound selected key old
      omega
  · intro selected other key one two
    by_cases first : selected = token
    · subst selected
      have equal : key = ⟨state.deferreds.cells.length⟩ := Option.some.inj (by simpa only [publish, ↓reduceIte] using one.symm)
      by_cases second : other = token
      · exact second.symm
      · have old : world.keys other = some key := by simpa only [publish, if_neg second] using two
        have small := bound other key old
        rw [equal] at small
        exact False.elim (Nat.lt_irrefl _ small)
    · by_cases second : other = token
      · subst other
        have equal : key = ⟨state.deferreds.cells.length⟩ := Option.some.inj (by simpa only [publish, ↓reduceIte] using two.symm)
        have old : world.keys selected = some key := by simpa only [publish, if_neg first] using one
        have small := bound selected key old
        rw [equal] at small
        exact False.elim (Nat.lt_irrefl _ small)
      · exact unique selected other key
          (by simpa only [publish, if_neg first] using one)
          (by simpa only [publish, if_neg second] using two)

end Test.Dogfood.Proofs.QueueWorkersRequestKeys
