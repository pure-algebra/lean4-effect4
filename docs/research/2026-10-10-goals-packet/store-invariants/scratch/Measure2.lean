import Test.Dogfood.Scenario.Atomic

open Effect4 Effect4.Program Test.Dogfood.Scenario.Atomic

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- The whole build: elaboration, then the checker's admission.
example : (Effect4.Api.Author.build (shop .none)).toOption.isSome = true := by decide
