import Test.Dogfood.Scenario.Routing

open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario Test.Dogfood.Scenario.Routing

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def progOf (token : String) (id : Nat) (idText : String) : Api.Program :=
  match Authoring.elaborateModule (request token id idText) with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

set_option pp.deepTerms true
set_option pp.maxSteps 100000
#reduce (proofs := false) (types := false) fun (id : Nat) (idText : String) => progOf "secret" id idText
