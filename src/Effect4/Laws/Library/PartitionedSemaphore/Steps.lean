import Effect4.Library.PartitionedSemaphore.Steps
import Effect4.Laws.Library.PartitionedSemaphore.Data
import Effect4.Laws.Step

/-! The source reading laws consume shared Step.sound and the independent value equations.
The typing laws read step-language-typed at the four concrete stored steps.
The aggregate names only the four scalar source observations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Effect4.PartitionedSemaphore
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Model (Counts)

namespace Model

section Reading
variable {env : Env} {path : List Nat} {vals : List Effect4.Store.Val}

/-- The construction source reads the independent model's derived image. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem initial_reads (capacity : Nat) {source : TermSrc}
    (h : Reads source env path vals (.nat capacity)) :
    Reads (initialStep source) env path vals ((Modeled.image Counts).toVal (Model.initial capacity)) := by
  have reading := Step.sound (Γ := Data.InitialInputs.types) Leaves.refused (input_values% (Data.InitialInputs) (Leaves.refused) {capacity := capacity}) (Input.reads_cons h Input.reads_nil) Data.initial rfl
  rw [initial_eval] at reading
  exact reading

/-- The availability source reads the model's scalar reply. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem available_reads (s : Counts) {source : TermSrc}
    (h : Reads source env path vals ((Modeled.image Counts).toVal s)) :
    Reads (availableStep source) env path vals (.nat (Model.available s)) := by
  have reading := Step.sound (Γ := Data.CellInputs.types) Leaves.refused (input_values% (Data.CellInputs) (Leaves.refused) {cell := encoded s}) (Input.reads_cons h Input.reads_nil) Data.available rfl
  rw [available_eval] at reading
  exact reading

/-- The attempted take reads the model's reply and final scalar record. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem tryTake_reads (s : Counts) (n : Nat) {amount source : TermSrc}
    (hn : Reads amount env path vals (.nat n))
    (hs : Reads source env path vals ((Modeled.image Counts).toVal s)) :
    Reads (tryTakeStep amount source) env path vals
      ((Effect4.Store.Image.tuple2 Effect4.Store.Image.bool (Modeled.image Counts)).toVal (Model.tryTake s n)) := by
  have reading := Step.sound Leaves.refused (requests s n)
    (Input.reads_cons hn (Input.reads_cons hs Input.reads_nil)) Data.tryTake rfl
  rw [tryTake_eval] at reading
  exact reading

/-- Only the source's waiting branch consumes this reservation connector. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem reserve_reads (s : Counts) (n : Nat) {amount source : TermSrc}
    (hn : Reads amount env path vals (.nat n))
    (hs : Reads source env path vals ((Modeled.image Counts).toVal s))
    (insufficient : s.available < n) (capacity : n ≤ s.capacity) :
    Reads (reserveStep amount source) env path vals
      ((Effect4.Store.Image.tuple2 Effect4.Store.Image.nat (Modeled.image Counts)).toVal (Model.reserve s n)) := by
  have reading := Step.sound Leaves.refused (requests s n)
    (Input.reads_cons hn (Input.reads_cons hs Input.reads_nil)) Data.reserve rfl
  rw [reserve_eval s n insufficient capacity] at reading
  exact reading
end Reading

/-- The four source readings observe the independent scalar model.
Reservation retains the insufficient-availability and within-capacity branch premises.
This claim excludes identities, registration, cancellation, delivery, wrappers, and host execution. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem bookkeeping_agrees :
    (∀ (capacity : Nat) (source : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), Reads source env path vals (.nat capacity) →
      Reads (initialStep source) env path vals ((Modeled.image Counts).toVal (Model.initial capacity))) ∧
    (∀ (s : Counts) (source : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), Reads source env path vals ((Modeled.image Counts).toVal s) →
      Reads (availableStep source) env path vals (.nat (Model.available s))) ∧
    (∀ (s : Counts) (n : Nat) (amount source : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), Reads amount env path vals (.nat n) →
      Reads source env path vals ((Modeled.image Counts).toVal s) →
      Reads (tryTakeStep amount source) env path vals
        ((Effect4.Store.Image.tuple2 Effect4.Store.Image.bool (Modeled.image Counts)).toVal (Model.tryTake s n))) ∧
    (∀ (s : Counts) (n : Nat) (amount source : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), Reads amount env path vals (.nat n) →
      Reads source env path vals ((Modeled.image Counts).toVal s) →
      s.available < n → n ≤ s.capacity →
      Reads (reserveStep amount source) env path vals
        ((Effect4.Store.Image.tuple2 Effect4.Store.Image.nat (Modeled.image Counts)).toVal (Model.reserve s n))) :=
  ⟨fun capacity _ _ _ _ h => initial_reads capacity h,
   fun s _ _ _ _ h => available_reads s h,
   fun s n _ _ _ _ _ hn hs => tryTake_reads s n hn hs,
   fun s n _ _ _ _ _ hn hs insufficient capacity => reserve_reads s n hn hs insufficient capacity⟩

end Model

section Typing
variable {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
  {env : Env} {path : List Nat} {types : List Ty}
include atoms
/-- Consumer of step-language-typed, R4, at this construction. -/
@[semantics "store-typing" (requirement := R4)]
theorem initial_types {source : TermSrc} (h : TypesEach sig source env path types .nat) :
    TypesEach sig (initialStep source) env path types countsTy :=
  Step.typed_of_normal sig atoms (Input.types_cons h Input.types_nil) Data.initial rfl

/-- Consumer of step-language-typed, R4, at this scalar read. -/
@[semantics "store-typing" (requirement := R4)]
theorem available_types {source : TermSrc} (h : TypesEach sig source env path types countsTy) :
    TypesEach sig (availableStep source) env path types .nat :=
  Step.typed_of_normal sig atoms (Input.types_cons h Input.types_nil) Data.available rfl

/-- Consumer of step-language-typed, R4, at this attempted take. -/
@[semantics "store-typing" (requirement := R4)]
theorem tryTake_types {amount source : TermSrc} (hn : TypesEach sig amount env path types .nat)
    (hs : TypesEach sig source env path types countsTy) :
    TypesEach sig (tryTakeStep amount source) env path types (.prod .bool countsTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons hn (Input.types_cons hs Input.types_nil)) Data.tryTake rfl

/-- Consumer of step-language-typed, R4, at this branch arithmetic. -/
@[semantics "store-typing" (requirement := R4)]
theorem reserve_types {amount source : TermSrc} (hn : TypesEach sig amount env path types .nat)
    (hs : TypesEach sig source env path types countsTy) :
    TypesEach sig (reserveStep amount source) env path types (.prod .nat countsTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons hn (Input.types_cons hs Input.types_nil)) Data.reserve rfl
end Typing


end Effect4.PartitionedSemaphore
