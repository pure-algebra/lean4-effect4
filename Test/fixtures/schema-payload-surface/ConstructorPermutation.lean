import Test.Schema.PayloadSurface

namespace Test.Schema.PayloadSurface.Mutants.ConstructorPermutation

inductive Subject where
  | second (value : Bool)
  | first

#effect4_check_inductive_surface
  Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject
  levels 0 params 0 indices 0
  family [Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject] where
  | Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject.first :
      Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject
  | Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject.second :
      Bool → Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject

end Test.Schema.PayloadSurface.Mutants.ConstructorPermutation
