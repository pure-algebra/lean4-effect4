import Effect4.Laws.Program.AnswerSlots.InitializationExact
import Effect4.Laws.Program.AnswerSlots.PrefixStable
import Effect4.Laws.Program.AnswerSlots.AllocationProvenance
import Test.Dogfood.Scenario.Atomic.Model
import Test.Dogfood.Proofs.HostTimeoutSource
import Effect4.Laws.Author
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: store-typing R4, serving Atomic.shop_stages and Timeout numeric histories.
Question: the authored shop and fetch initialize the exact three cells read by their observations.
Reach: actual source binders, their closed initializer values and root binding positions.
Consumer: the shared bare AllocationAdapter and its actual entry boundary.
These certificates establish no admitted history or scheduler progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Scenario.RootCells
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
/-- The request at a root binder, read from the source. -/
def requestAt (root : NativeEff) (index : Nat) : Term :=
  match Node.at_ (.eff root) (List.replicate index 1) with
  | some (.eff (.bind (.perform .refMake term) _)) => term
  | _ => .lit .unit

/-- The rest after a root binder, read from the source. -/
def tailAt (root : NativeEff) (index : Nat) : NativeEff :=
  match Node.at_ (.eff root) (List.replicate index 1) with
  | some (.eff (.bind _ rest)) => rest
  | _ => .succeed (.lit .unit)

/-- The Atomic shop's elaborated tree. -/
def shop : NativeEff :=
  (Authoring.elaborateModule (Test.Dogfood.Scenario.Atomic.shop .none)).toOption.getD (.succeed (.lit .unit))

theorem shop_head (index : Nat) (small : index < 3) : ∃ tail,
    Node.at_ (.eff shop) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake (requestAt shop index)) tail)) := by
  rcases index with _ | _ | _ | index
  · exact ⟨tailAt shop 0, by kernel_rfl⟩
  · exact ⟨tailAt shop 1, by kernel_rfl⟩
  · exact ⟨tailAt shop 2, by kernel_rfl⟩
  · exact (show False by omega).elim

theorem shop_closed (index : Nat) (small : index < 3) (env : List Val) :
    evalTerm env (requestAt shop index) = some ((evalTerm [] (requestAt shop index)).getD .unit) := by
  rcases index with _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

def atomic : AnswerSlots.Initialization shop where
  width := 3
  bindings := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩]
  request := requestAt shop
  initial := fun index => (evalTerm [] (requestAt shop index)).getD .unit
  head := shop_head
  closed := shop_closed
  next := by
    intro index small
    rcases index with _ | _ | _ | index
    · rfl
    · rfl
    · rfl
    · exact (show False by omega).elim

theorem fetch_head (index : Nat) (small : index < 3) : ∃ tail,
    Node.at_ (.eff Test.Dogfood.Proofs.HostTimeoutSource.program) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake
        (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index)) tail)) := by
  rcases index with _ | _ | _ | index
  · exact ⟨tailAt Test.Dogfood.Proofs.HostTimeoutSource.program 0, by kernel_rfl⟩
  · exact ⟨tailAt Test.Dogfood.Proofs.HostTimeoutSource.program 1, by kernel_rfl⟩
  · exact ⟨tailAt Test.Dogfood.Proofs.HostTimeoutSource.program 2, by kernel_rfl⟩
  · exact (show False by omega).elim

theorem fetch_closed (index : Nat) (small : index < 3) (env : List Val) :
    evalTerm env (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index) =
      some ((evalTerm [] (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index)).getD .unit) := by
  rcases index with _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

def timeout : AnswerSlots.Initialization Test.Dogfood.Proofs.HostTimeoutSource.program where
  width := 3
  bindings := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩]
  request := requestAt Test.Dogfood.Proofs.HostTimeoutSource.program
  initial := fun index => (evalTerm [] (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index)).getD .unit
  head := fetch_head
  closed := fetch_closed
  next := by
    intro index small
    rcases index with _ | _ | _ | index
    · rfl
    · rfl
    · rfl
    · exact (show False by omega).elim


/-- A successful Atomic build retains the source tree certified by the common initializer. -/
theorem shop_eq (built : Api.Built)
    (accepted : Api.Author.build (Atomic.shop .none) = .ok built) : shop = built.program := by
  unfold shop
  rw [(Api.Author.build_retains accepted).1]
  rfl

/-- The common initializer certificate applies to every successful Atomic shop build. -/
def atomicBuilt (built : Api.Built) (accepted : Api.Author.build (Atomic.shop .none) = .ok built) :
    AnswerSlots.Initialization built.program where
  width := atomic.width
  bindings := atomic.bindings
  request := atomic.request
  initial := atomic.initial
  head := by
    intro index small
    obtain ⟨tail, found⟩ := atomic.head index small
    have moved := congrArg (fun program : NativeEff => Node.at_ (.eff program) (List.replicate index 1))
      (shop_eq built accepted)
    exact ⟨tail, moved.symm.trans found⟩
  closed := atomic.closed
  next := atomic.next

/-- The fetch's actual reference heap is the numeric phase's three declared initial cells. -/
theorem timeout_values : AnswerSlots.Initialization.values timeout 3 = [.nat 0, .list [], .list []] := by
  kernel_rfl

/-- Atomic uses the common reference-only adapter at its actual built source and row table. -/
def atomicAdapter (built : Api.Built) (accepted : Api.Author.build (Atomic.shop .none) = .ok built) :
    AnswerSlots.AllocationAdapter.Spec :=
  AnswerSlots.AllocationAdapter.bareSpec built.program built.table (atomicBuilt built accepted)
    (by change 0 < 3; decide) rfl

/-- Timeout uses the same reference-only adapter and its actual source cells. -/
def timeoutAdapter : AnswerSlots.AllocationAdapter.Spec :=
  AnswerSlots.AllocationAdapter.bareSpec Test.Dogfood.Proofs.HostTimeoutSource.program [] timeout
    (by decide) rfl

end Test.Dogfood.Scenario.RootCells
