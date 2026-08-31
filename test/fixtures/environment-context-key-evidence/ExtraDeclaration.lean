import Effect4Test.Environment.ContextKeyAssurance

namespace Effect4Test.Environment.ContextKeyEvidenceMutation

def expected : Nat := 0
def extra : Nat := 1

end Effect4Test.Environment.ContextKeyEvidenceMutation

#effect4_check_exact_current_module_surface [
  Effect4Test.Environment.ContextKeyEvidenceMutation.expected]
