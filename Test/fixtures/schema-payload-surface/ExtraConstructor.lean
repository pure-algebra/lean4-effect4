import Test.Schema.PayloadSurface

namespace Test.Schema.PayloadSurface.Mutants.ExtraConstructor

inductive Subject where
  | first
  | second (value : Bool)
  | extra (value : Nat)

#effect4_check_inductive_surface
  Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject
  levels 0 params 0 indices 0
  family [Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject] where
  | Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject.first :
      Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject
  | Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject.second :
      Bool → Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject

end Test.Schema.PayloadSurface.Mutants.ExtraConstructor
