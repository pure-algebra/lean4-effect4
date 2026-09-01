import Effect4Test.Concurrency.FiberAssurance

/-! `Effect4.Step` exists, but this mutant assigns it to the test module. -/

#effect4_check_fiber_declaration_owners
  Effect4Test.Concurrency.FiberAssuranceMutation [
    Effect4.Step]
