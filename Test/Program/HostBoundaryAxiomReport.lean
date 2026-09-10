import Effect4.Laws.Program.HostBoundary

/-! S6b-0 fresh dependency receipt. These commands must run under the existing
propext/Quot.sound ceiling; the report is not a replacement for AxiomGate. -/

#print axioms Effect4.Program.HostInputCheck
#print axioms Effect4.Program.HostBoundaryResult
#print axioms Effect4.Program.HostBoundaryResult.ofAttempt
#print axioms Effect4.Program.HostBoundaryResult.admitted_without_attempt
#print axioms Effect4.Program.HostBoundaryResult.malformed_retains_state
#print axioms Effect4.Program.HostBoundaryResult.outside_profile_retains_state
#print axioms Effect4.Program.HostBoundaryResult.completed_retains_resulting_state
#print axioms Effect4.Program.Profile.Scalar.checkRequest
#print axioms Effect4.Program.Profile.Scalar.poll
#print axioms Effect4.Program.Profile.Resource.checkRequest
#print axioms Effect4.Program.Profile.Resource.poll
#print axioms Effect4.Program.Profile.Resource.OwnsAll
#print axioms Effect4.Program.Profile.Resource.CleanupComplete
#print axioms Effect4.Program.Profile.Resource.owned_cleanup_closes_slots
#print axioms Effect4.Program.Profile.Resource.terminal_observe
#print axioms Effect4.Program.Profile.Resource.related_open_resource
#print axioms Effect4.Program.Profile.Resource.open_resource_not_terminal
#print axioms Effect4.Program.Profile.Choice.spec
#print axioms Effect4.Program.Profile.Choice.lawful
#print axioms Effect4.Program.Profile.Choice.left_step
#print axioms Effect4.Program.Profile.Choice.right_step
#print axioms Effect4.Program.Profile.Choice.not_deterministic
#print axioms Effect4.Program.DeterministicHostSpec
#print axioms Effect4.Program.Profile.Scalar.deterministic
#print axioms Effect4.Program.Profile.Resource.deterministic
#print axioms Effect4.Program.Profile.Resource.closedUse
#print axioms Effect4.Program.Profile.Resource.doubleRelease
#print axioms Effect4.Program.Profile.Resource.closed_use_dies
#print axioms Effect4.Program.Profile.Resource.double_release_dies
