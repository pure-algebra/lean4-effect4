import Test.Data.RowAssurance

namespace Test.Data.RowAssuranceMutation

def expected : Nat := 0

end Test.Data.RowAssuranceMutation

#effect4_check_exact_current_module_surface [
  Test.Data.RowAssuranceMutation.expected,
  Test.Data.RowAssuranceMutation.missing]
