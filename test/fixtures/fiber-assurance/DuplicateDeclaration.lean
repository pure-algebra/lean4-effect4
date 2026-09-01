import Effect4Test.Concurrency.FiberAssurance

namespace Effect4Test.Concurrency.FiberAssuranceMutation

def expected : Nat := 0

end Effect4Test.Concurrency.FiberAssuranceMutation

/-! A duplicate cannot stand in for a second declaration in an exact census. -/

#effect4_check_exact_current_fiber_module_surface [
  Effect4Test.Concurrency.FiberAssuranceMutation.expected,
  Effect4Test.Concurrency.FiberAssuranceMutation.expected]
