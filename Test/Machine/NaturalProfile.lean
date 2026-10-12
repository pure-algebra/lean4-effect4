import Effect4.Laws.Machine.IntegerProfile
import Effect4.Program.Profile

/-!
Concept: translation-simulation R8.
Question: profile-mul-exact at the actual represented natural multiplication.
The reader uses the declared rc.112 bound; controls retain its first refused product.
This battery establishes no target-runtime correspondence.
-/
set_option autoImplicit false
namespace Test.Machine.NaturalProfile
open Effect4 Effect4.Program

/-- The actual atom returns the largest admitted natural product. -/
theorem boundary_product :
    NativeAtom.eval .mul [.nat rc112.natBound, .nat 1] = some (.nat rc112.natBound) ∧
      Within rc112.natBound (.nat rc112.natBound) = true :=
  (mulIn_eq_some_iff rc112.natBound rc112.natBound 1 rc112.natBound).mp (by decide)

#guard scaleIn rc112.natBound 0 rc112.natBound = some 0
#guard scaleIn rc112.natBound 4503599627370496 2 = none
#guard scaleIn rc112.natBound 134217729 134217729 = none
#guard NativeAtom.eval .mul [.nat 134217729, .nat 134217729] = some (.nat 18014398777917441)

end Test.Machine.NaturalProfile
