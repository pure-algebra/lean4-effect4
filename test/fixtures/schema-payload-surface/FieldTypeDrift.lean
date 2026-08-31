import Effect4Test.Schema.PayloadSurface

namespace Effect4Test.Schema.PayloadSurface.Mutants.FieldTypeDrift

structure Subject where
  value : Nat

#effect4_check_structure_surface
  Effect4Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject
  levels 0 params 0
  constructor |
    Effect4Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject.mk :
      String → Effect4Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject
  fields
  | Effect4Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject.value :
      Effect4Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject → String

end Effect4Test.Schema.PayloadSurface.Mutants.FieldTypeDrift
