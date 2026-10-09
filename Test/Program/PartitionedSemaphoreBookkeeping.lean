import Effect4.Author
import Effect4.Library
import Effect4.Laws.Author
import Effect4.Laws.Library.PartitionedSemaphore.Steps

/-!
Readers of partitioned-semaphore-bookkeeping and step-language-typed at concrete scalar callers.
The aggregate supplies every reading, so these readers also exercise its registry-facing statement.
The reservation reader supplies both branch premises on a real state.
No reader states a new general law or a wrapper observation.
-/
set_option autoImplicit false
namespace Test.Program.PartitionedSemaphoreBookkeeping
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules Effect4.Schema
open Effect4.PartitionedSemaphore

example (env : Env) (path : List Nat) (vals : List Store.Val) :
    Reads (initialStep (nat 5)) env path vals
      ((Modeled.image Model.Counts).toVal (Model.initial 5)) :=
  Model.bookkeeping_agrees.1 5 (nat 5) env path vals (reads_nat 5 env path vals)

example (env : Env) (path : List Nat) (vals : List Store.Val) :
    Reads (availableStep (initialStep (nat 5))) env path vals (.nat 5) :=
  Model.bookkeeping_agrees.2.1 (Model.initial 5) (initialStep (nat 5)) env path vals
    (Model.bookkeeping_agrees.1 5 (nat 5) env path vals (reads_nat 5 env path vals))

example (env : Env) (path : List Nat) (vals : List Store.Val) :
    Reads (tryTakeStep (nat 3) (initialStep (nat 5))) env path vals
      ((Store.Image.tuple2 Store.Image.bool (Modeled.image Model.Counts)).toVal
        (true, (⟨5, 2, 0⟩ : Model.Counts))) :=
  Model.bookkeeping_agrees.2.2.1 (Model.initial 5) 3 (nat 3) (initialStep (nat 5)) env path vals
    (reads_nat 3 env path vals)
    (Model.bookkeeping_agrees.1 5 (nat 5) env path vals (reads_nat 5 env path vals))

/-- A real branch state with capacity five and two permits still available. -/
def waitingBranch : TermSrc := recordSet (initialStep (nat 5)) "available" (nat 2)

example : Reads (reserveStep (nat 4) waitingBranch) {} [] []
    ((Store.Image.tuple2 Store.Image.nat (Modeled.image Model.Counts)).toVal
      (2, (⟨5, 0, 2⟩ : Model.Counts))) := by
  have cell : Reads waitingBranch {} [] [] ((Modeled.image Model.Counts).toVal ⟨5, 2, 0⟩) :=
    ⟨_, rfl, rfl⟩
  exact Model.bookkeeping_agrees.2.2.2 ⟨5, 2, 0⟩ 4 (nat 4) waitingBranch {} [] []
    (reads_nat 4 {} [] []) cell (by decide) (by decide)

example (env : Env) (path : List Nat) (types : List Ty) :
    TypesEach nativeSignature (initialStep (nat 5)) env path types countsTy :=
  initial_types nativeSignature rfl (types_nat 5)

example (env : Env) (path : List Nat) (types : List Ty) :
    TypesEach nativeSignature (availableStep (initialStep (nat 5))) env path types .nat :=
  available_types nativeSignature rfl (initial_types nativeSignature rfl (types_nat 5))

example (env : Env) (path : List Nat) (types : List Ty) :
    TypesEach nativeSignature (tryTakeStep (nat 3) (initialStep (nat 5))) env path types
      (.prod .bool countsTy) :=
  tryTake_types nativeSignature rfl (types_nat 3) (initial_types nativeSignature rfl (types_nat 5))

-- Typing alone does not prove that the waiting branch applies to this source.
example (env : Env) (path : List Nat) (types : List Ty) :
    TypesEach nativeSignature (reserveStep (nat 3) (initialStep (nat 5))) env path types
      (.prod .nat countsTy) :=
  reserve_types nativeSignature rfl (types_nat 3) (initial_types nativeSignature rfl (types_nat 5))

end Test.Program.PartitionedSemaphoreBookkeeping
