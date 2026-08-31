import Effect4Test.Schema.PayloadSurface

namespace Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited

inductive Subject where
  | first
  | second (value : Bool)
  | extra (impossible : Empty)

#effect4_check_inductive_surface
  Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject
  levels 0 params 0 indices 0
  family [Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject] where
  | Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject.first :
      Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject
  | Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject.second :
      Bool → Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited.Subject

end Effect4Test.Schema.PayloadSurface.Mutants.ExtraUninhabited
