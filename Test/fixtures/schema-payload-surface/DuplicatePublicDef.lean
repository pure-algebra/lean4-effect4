import Test.Schema.PayloadSurface

/-! Synthetic ordinary public type-valued definition after the frozen module. -/

namespace Effect4

def DuplicateReferenceKey : Type := ReferenceKey

end Effect4

#effect4_check_public_type_surface Effect4.DuplicateReferenceKey []
