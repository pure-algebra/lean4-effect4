module
import Init

private noncomputable def hiddenChoice : Nat :=
  Classical.choice (show Nonempty Nat from ⟨0⟩)

public def clean : Nat := 7
