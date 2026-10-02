import Test.All
import Test.Program.ExitTypeLane
import Test.Api.TraceOrigin
import Test.Api.SupervisionContract
import Test.Machine.StepInvRulesRed
import Test.Audit.ExhaustiveFixture
import Test.Audit.TraversalFixture
import Test.Audit.TraversalCensus
import Test.Program.LayerSharingCertificate

/-!
# Effect4 slow battery

The batteries out of the default build (owner, 2026-10-02): long finite runs, the diagnostic trace
laws and the traversal census, each minutes where a contract takes seconds. `make check-slow` builds
this root at a sweep; the default `lake build` reaches `Test.All` only. The module-closure gate
admits exactly these files outside `Test.All` (`slowLane`, `Test/Audit/AxiomGate.lean`), and the
gate below audits them with everything `Test.All` reaches.
-/

#effect4_axiom_gate
