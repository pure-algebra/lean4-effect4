import Effect4Test.Schema.PayloadSurface

namespace Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation

inductive Subject where
  | second (value : Bool)
  | first

#effect4_check_inductive_surface
  Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject
  levels 0 params 0 indices 0
  family [Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject] where
  | Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject.first :
      Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject
  | Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject.second :
      Bool → Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation.Subject

end Effect4Test.Schema.PayloadSurface.Mutants.ConstructorPermutation
