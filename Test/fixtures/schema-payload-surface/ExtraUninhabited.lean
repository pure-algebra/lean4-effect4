import Test.Schema.PayloadSurface

namespace Test.Schema.PayloadSurface.Mutants.ExtraUninhabited

inductive Subject where
  | first
  | second (value : Bool)
  | extra (impossible : Empty)

#effect4_check_inductive_surface
  Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject
  levels 0 params 0 indices 0
  family [Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject] where
  | Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject.first :
      Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject
  | Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject.second :
      Bool → Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject

end Test.Schema.PayloadSurface.Mutants.ExtraUninhabited
