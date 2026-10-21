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
    NativeAtom.eval .mul [.nat safeBound, .nat 1] = some (.nat safeBound) ∧
      Within rc112 (.nat safeBound) = true :=
  (mulIn_eq_some_iff rc112 safeBound 1 safeBound).mp (by decide)

#guard scaleIn rc112 0 safeBound = some 0
#guard scaleIn rc112 4503599627370496 2 = none
#guard scaleIn rc112 134217729 134217729 = none
-- control: a profile with no bound, the native one's, admits the product rc.112 refuses
#guard scaleIn { rc112 with natBound := none } 134217729 134217729 = some 18014398777917441
#guard NativeAtom.eval .mul [.nat 134217729, .nat 134217729] = some (.nat 18014398777917441)

end Test.Machine.NaturalProfile
