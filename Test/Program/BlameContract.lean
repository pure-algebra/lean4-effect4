import Effect4.Api
import Effect4.Laws.Api.Blame

/-!
# Blame contract — the refusal is located and named (DI-86)

`Api.explain` (`src/Effect4/Api.lean`) projects the one checker: the path of the deepest node
whose own rule refuses, and that rule's reason (`TypeReason`, `Program/Typing/Blame.lean`).
The pins walk a refusal down through `bind`, `suspend`, `catchCause`, `branch` and a generator
body, and the law `Api.explain_none_iff` (`Laws/Api/Blame.lean`) is what makes the projection
the checker's rather than a second checker.
-/

set_option autoImplicit false

namespace Test.Program.BlameContract

open Effect4 Effect4.Program Effect4.Api

/-- The root fails at a type the error alphabet does not admit. -/
def refused : Api.Program := .fail (.lit (.bool true))

#guard Api.wellTyped refused = false
#guard Api.explain refused = some ⟨[], .errorNotAdmitted .bool⟩
#guard Api.blame refused = some []

/-! ## The path follows the checker's environment -/

#guard Api.blame (.bind (.succeed (.lit (.nat 1))) refused) = some [1]
#guard Api.blame (.catchCause (.suspend refused) (.succeed (.lit .unit))) = some [0, 0]
#guard Api.blame (.catchCause (.succeed (.lit .unit)) refused) = some [1]
#guard Api.blame (.branch (.lit (.bool true)) (.succeed (.lit .unit)) refused) = some [1]
#guard Api.blame (.onExit (.succeed (.lit .unit)) (.bind refused (.succeed (.lit .unit)))) = some [1, 0]

/-! ## The reason is the node's own rule -/

#guard Api.explain (.succeed (.var 0)) = some ⟨[], .term (.var 0)⟩
#guard Api.explain (.branch (.lit (.nat 1)) (.succeed (.lit .unit)) (.succeed (.lit .unit)))
  = some ⟨[], .predicateNotBool .nat⟩
#guard match Api.explain (.perform .refGet (.lit (.nat 1))) with
  | some ⟨[], .requestNotSubtype _ _ _⟩ => true
  | _ => false
#guard Api.explain (.gen (.cons (.ret (.lit .unit)) (.cons (.bindYield (.succeed (.lit .unit))) .nil)))
  = some ⟨[0, 0], .returnNotLast⟩
#guard Api.explain (.gen (.cons .breakLoop .nil)) = some ⟨[0, 0], .breakOutsideLoop⟩
#guard Api.explain (.provideLayer (.mergeAll .nil) false (.succeed (.lit .unit)))
  = some ⟨[0, 0], .mergeAllEmpty⟩
-- A reference with no preceding target is refused at the root, before typing.
#guard Api.explain (.provideLayer (.ref [0]) false (.succeed (.lit .unit)))
  = some ⟨[], .referencesIllFormed⟩

/-! ## A typed program has no refusal -/

def typed : Api.Program := .bind (.perform .refMake (.lit (.nat 1))) (.perform .refGet (.var 0))

#guard Api.wellTyped typed
#guard Api.explain typed = none
#guard Api.blame typed = none

#print axioms Effect4.Api.explain_none_iff
#print axioms Effect4.Program.explain_none_iff

end Test.Program.BlameContract
