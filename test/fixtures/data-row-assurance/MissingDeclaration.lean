import Effect4Test.Data.RowAssurance

namespace Effect4Test.Data.RowAssuranceMutation

def expected : Nat := 0

end Effect4Test.Data.RowAssuranceMutation

#effect4_check_exact_current_module_surface [
  Effect4Test.Data.RowAssuranceMutation.expected,
  Effect4Test.Data.RowAssuranceMutation.missing]
