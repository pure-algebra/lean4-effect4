import Effect4.Laws.Program.Typed.Assembly

-- Eight authorized existing bodies, seven legacy plus E's strongExit_mono adapter.
#print axioms Effect4.Program.Typed.strongExit_success
#print axioms Effect4.Program.Typed.strongExit_of_clean
#print axioms Effect4.Program.Typed.cleanExit_of_never
#print axioms Effect4.Program.Typed.strongExit_bool
#print axioms Effect4.Program.Typed.settling_fork
#print axioms Effect4.Program.Typed.strongExit_mono
#print axioms Effect4.Program.Typed.strongExit_failure_of_error
#print axioms Effect4.Program.Typed.popR_typed

-- Seven new local exclusion helpers; none discharges a transition obligation.
#print axioms Effect4.Program.Typed.noShapeDefect_of_interrupts
#print axioms Effect4.Program.Typed.noShapeDefect_stripFail
#print axioms Effect4.Program.Typed.noShapeDefect_combine
#print axioms Effect4.Program.Typed.noShapeDefect_sanitize
#print axioms Effect4.Program.Typed.recorded_noShapeDefect
#print axioms Effect4.Program.Typed.pendingCause_noShapeDefect
#print axioms Effect4.Program.Typed.sanitize_noShapeDefect
