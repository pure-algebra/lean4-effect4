import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual restoring masks serve both Timeout numeric endpoint goals without granting failures to read or unit classes.
Consumer: the source-sensitive uniform saved edge and actual value-replacement producer.
Reach: the existing numeric value and cause predicates, with an actual clean recorded cause.
Limit: source and native history must establish which class owns each actual restoring mask.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberMaskClass
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow

/-- Read and unit classes execute inside their actual protected numeric region. -/
def Restorable : Kind → Prop
  | .read _ | .unit _ | .paused _ _ => False
  | _ => True

/-- A real restoring-mask class turns its successful value evidence into the actual clean interruption permission. -/
theorem value_recorded (state : Stores) (kind : Kind) (value : Val) (cause : CauseV)
    (restorable : Restorable kind) (good : ValueAt state kind value)
    (clean : HostTimeoutNumberFlow.NoTypedFailure cause) : CauseAt state kind cause := by
  cases kind with
  | fresh phase => exact ⟨good, clean⟩
  | attempt before entered own => exact Or.inl good
  | read phase => exact False.elim restorable
  | unit phase => exact False.elim restorable
  | countUnit phase => exact ⟨good.1, clean⟩
  | paused phase incoming => exact False.elim restorable
  | before phase => exact good
  | cleanupExit phase own => exact good
  | published phase =>
    obtain ⟨selected, heap, returned⟩ := good
    exact ⟨selected, heap, typedFrom_clean selected cause clean⟩

/-- A real restoring mask retains its heap and selected-exit facts when its actual clean cause replaces failure. -/
theorem cause_recorded (state : Stores) (kind : Kind) (cause recorded : CauseV)
    (restorable : Restorable kind) (good : CauseAt state kind cause)
    (clean : HostTimeoutNumberFlow.NoTypedFailure recorded) : CauseAt state kind recorded := by
  cases kind with
  | fresh phase => exact ⟨good.1, clean⟩
  | attempt before entered own =>
    rcases good with cleaned | ⟨heap, quiet⟩
    · exact Or.inl cleaned
    · exact Or.inr ⟨heap, clean⟩
  | read phase => exact False.elim good
  | unit phase => exact False.elim good
  | countUnit phase => exact ⟨good.1, clean⟩
  | paused phase incoming => exact False.elim restorable
  | before phase => exact good
  | cleanupExit phase own => exact good
  | published phase =>
    obtain ⟨selected, heap, origin⟩ := good
    exact ⟨selected, heap, typedFrom_clean selected recorded clean⟩

end Test.Dogfood.Proofs.HostTimeoutNumberMaskClass
