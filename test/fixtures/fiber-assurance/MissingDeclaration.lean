import Effect4Test.Concurrency.FiberAssurance

namespace Effect4Test.Concurrency.FiberAssuranceMutation

def expected : Nat := 0

end Effect4Test.Concurrency.FiberAssuranceMutation

#effect4_check_exact_current_fiber_module_surface [
  Effect4Test.Concurrency.FiberAssuranceMutation.expected,
  Effect4Test.Concurrency.FiberAssuranceMutation.missing]
