import Effect4Test.Schema.PayloadSurface

/-! Synthetic D7 constructor equation declared outside `Effect4.Schema.Check`. -/

namespace Effect4.PayloadSurfaceMutation

theorem fieldAdmissible_reference_iff : True ↔ True := Iff.rfl

end Effect4.PayloadSurfaceMutation

#effect4_check_declaration_owners Effect4.Schema.Check [
  Effect4.PayloadSurfaceMutation.fieldAdmissible_reference_iff]
