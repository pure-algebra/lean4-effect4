import Test.Dogfood.Scenario.Atomic.Store
import Test.Dogfood.Scenario.SourceOpportunity
open Effect4 Effect4.Program Test.Dogfood.Scenario
#eval Atomic.Store.shopProgram.map fun root =>
  (Node.addresses (.eff root)).filterMap fun path =>
    match Node.at_ (.eff root) path, SourceScope.levelAt (.eff root) 0 path with
    | some (.eff (.perform (.refUpdateWith term) _)), some level =>
        some (path, level, Atomic.requests.find? fun id => term == Atomic.Store.noteAt id level)
    | _, _ => none
