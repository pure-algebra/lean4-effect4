import Effect4Test.Data.RowAssurance

namespace Effect4Test.Data.RowAssuranceMutation

def expected : Nat := 0
def extra : Nat := 1

end Effect4Test.Data.RowAssuranceMutation

#effect4_check_exact_current_module_surface [
  Effect4Test.Data.RowAssuranceMutation.expected]
