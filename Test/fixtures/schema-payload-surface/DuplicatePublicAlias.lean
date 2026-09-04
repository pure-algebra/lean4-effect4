import Test.Schema.PayloadSurface

/-! Synthetic public carrier alias added after the frozen Payload module. -/

namespace Effect4

abbrev DuplicateReferenceKey := ReferenceKey

end Effect4

#effect4_check_public_type_surface Effect4.DuplicateReferenceKey []
