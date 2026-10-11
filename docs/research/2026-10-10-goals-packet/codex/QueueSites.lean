import Test.Dogfood.Scenario.Programs

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Effect4 Effect4.Program Test.Dogfood.Scenario.Programs

-- Finite source-location probe; no dynamic source-capture assertion.
#eval (Node.addresses (.eff (queueProgram 0))).filterMap fun path =>
  match (Node.eff (queueProgram 0)).at_ path with
  | some (.eff (.perform (.refModifyWith _) request)) => some (path, match request with | .var i => some i | _ => none)
  | _ => none
