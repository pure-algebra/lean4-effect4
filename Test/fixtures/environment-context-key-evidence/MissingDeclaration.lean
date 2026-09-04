import Test.Machine.Environment.ContextKeyAssurance

namespace Test.Environment.ContextKeyEvidenceMutation

def expected : Nat := 0

end Test.Environment.ContextKeyEvidenceMutation

#effect4_check_exact_current_module_surface [
  Test.Environment.ContextKeyEvidenceMutation.expected,
  Test.Environment.ContextKeyEvidenceMutation.missing]
