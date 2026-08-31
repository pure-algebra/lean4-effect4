import Effect4Test.Schema.PayloadSurface

/-! Synthetic D7 judgment declared outside `Effect4.Schema.Check`. -/

namespace Effect4.PayloadSurfaceMutation

def FieldAdmissible (_ : Effect4.Representation) : Prop := True

end Effect4.PayloadSurfaceMutation

#effect4_check_declaration_owners Effect4.Schema.Check [
  Effect4.PayloadSurfaceMutation.FieldAdmissible]
