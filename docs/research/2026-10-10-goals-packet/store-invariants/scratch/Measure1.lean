import Test.Dogfood.Scenario.Atomic

open Effect4 Effect4.Program Test.Dogfood.Scenario.Atomic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

-- Elaboration only: the kernel reduces the authoring functions of the shop.
example : (Authoring.elaborateModule (shop .none)).toOption.isSome = true := by decide
