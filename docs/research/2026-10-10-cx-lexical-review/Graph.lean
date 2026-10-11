import Effect4.Laws.Program.Typed.AdmittedSource
import ProofGraph.Why
import ProofGraph.Plan

-- Dependency evidence in the explicitly imported typed-run graph.
#plan_status Effect4.Program.Typed.invoke_arm Effect4.Program.Typed.m7_proved
#goal_impact Effect4.Program.Typed.invoke_arm
#why Effect4.Program.Typed.m7_proved Effect4.Program.Typed.invoke_arm
