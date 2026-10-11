/-!
Concept: scope-lifetime-finalization R11.
The existing Atomic cleanup source addresses live apart from their proof obligations.
Consumers: Cleanup.requestPath and the source opportunity address census.
The addresses remain unchanged.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.SourcePaths

/-- The finalizer source of each of the six request identities. -/
def requestPath : Nat → List Nat
  | 1 => [1, 1, 1, 1, 0, 0, 0]
  | 2 => [1, 1, 1, 1, 1, 0, 0, 0]
  | 3 => [1, 1, 1, 1, 1, 1, 0, 0, 0]
  | 4 => [1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
  | 5 => [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]

end Test.Dogfood.Scenario.Atomic.SourcePaths
