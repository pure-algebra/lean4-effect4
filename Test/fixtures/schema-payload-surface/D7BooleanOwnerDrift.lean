import Test.Schema.PayloadSurface

/-! Synthetic D7 Boolean decision declared outside `Effect4.Schema.Check`. -/

namespace Effect4.PayloadSurfaceMutation

def fieldAdmissible (_ : Effect4.Representation) : Bool := true

end Effect4.PayloadSurfaceMutation

#effect4_check_declaration_owners Effect4.Schema.Check [
  Effect4.PayloadSurfaceMutation.fieldAdmissible]
