import Effect4Test.Schema.PayloadSurface

/-! Synthetic D7 Boolean/reflection law declared outside `Effect4.Schema.Check`. -/

namespace Effect4.PayloadSurfaceMutation

theorem fieldAdmissible_iff : true = true ↔ True := by simp

end Effect4.PayloadSurfaceMutation

#effect4_check_declaration_owners Effect4.Schema.Check [
  Effect4.PayloadSurfaceMutation.fieldAdmissible_iff]
