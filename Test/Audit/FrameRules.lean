import Effect4.Laws.Auto.Frames

namespace Test.FrameRules
structure Pair where
  key : Nat
  value : Nat
structure Fits (s : Pair) : Prop where
  related : s.value = s.key
  nonzero : s.value > 0

#frame_rules Fits

-- Changing key requires a fresh proof of related, but the nonzero proof is reused.
example (s : Pair) (h : Fits s) (key : Nat) (relation : s.value = key) :
    Fits {s with key := key} := Fits.frame_key s h key relation

-- Changing value requires both clauses; no accessor about the old value closes either.
example (s : Pair) (h : Fits s) (value : Nat) (relation : value = s.key) (positive : value > 0) :
    Fits {s with value := value} := Fits.frame_value s h value relation positive

-- The tempting unconditional key frame is false on a concrete inhabited state.
example : Fits ⟨1, 1⟩ := ⟨rfl, by decide⟩
example : ¬ Fits ⟨2, 1⟩ := by
  intro h
  have impossible : (1 : Nat) = 2 := h.related
  contradiction

#print axioms Fits.frame_key
#print axioms Fits.frame_value
end Test.FrameRules
