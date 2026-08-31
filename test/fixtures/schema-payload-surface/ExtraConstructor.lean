import Effect4Test.Schema.PayloadSurface

namespace Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor

inductive Subject where
  | first
  | second (value : Bool)
  | extra (value : Nat)

#effect4_check_inductive_surface
  Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject
  levels 0 params 0 indices 0
  family [Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject] where
  | Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject.first :
      Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject
  | Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject.second :
      Bool → Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor.Subject

end Effect4Test.Schema.PayloadSurface.Mutants.ExtraConstructor
