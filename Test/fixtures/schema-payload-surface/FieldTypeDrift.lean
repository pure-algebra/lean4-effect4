import Test.Schema.PayloadSurface

namespace Test.Schema.PayloadSurface.Mutants.FieldTypeDrift

structure Subject where
  value : Nat

#effect4_check_structure_surface
  Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject
  levels 0 params 0
  constructor |
    Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject.mk :
      String → Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject
  fields
  | Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject.value :
      Test.Schema.PayloadSurface.Mutants.FieldTypeDrift.Subject → String

end Test.Schema.PayloadSurface.Mutants.FieldTypeDrift
