import MachineWorkersCapturedSlots

/-!
Finite control: the five initial bindings and lexical length permit a wrong release identity.
The ordinary current-code entry therefore excludes actual release destinations.
CapturedSlots retains the identity from the real acquired answer instead.
This control establishes no history failure or funding counterexample.
-/
open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario
open MachineWorkersSlots

private def wrongRelease : Point :=
  { (rootPoint 10) with
    path := Programs.crewAcquire 1 ++ [1]
    env := bindings ++ [.nat 9, .unit] }

#guard wrongRelease.env.take 5 == bindings
#guard SourceScope.levelAt (.eff (Programs.workersProgram 1)) 0 wrongRelease.path ==
  some wrongRelease.env.length
#guard wrongRelease.env[5]? == some (.nat 9)
#guard !(wrongRelease.path != Programs.crewAcquire 1 ++ [1] &&
  wrongRelease.path != Programs.crewAcquire 2 ++ [1])

